use crate::buckets::{Bucket, BucketId};
use crate::config::Args;
use crate::util::error;
use crate::verifier::{module_name, module_name_of_segments};
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Fun, Function, Krate, VirErr};
use vir::ast_util::{friendly_fun_name_crate_relative, parse_path_segments_from_user_str};

#[derive(Clone, Debug)]
pub enum UserFilter {
    /// No filter (i.e., verify everything)
    None,
    /// Verify modules
    Modules(Vec<ModuleId>),
    /// Verify the functions matched by any of the patterns, within these modules
    Function(Vec<ModuleId>, HashSet<Fun>),
}

type ModuleId = vir::ast::Idents;

fn root_module_id() -> ModuleId {
    Arc::new(vec![])
}

impl UserFilter {
    pub fn is_everything(&self) -> bool {
        matches!(self, UserFilter::None)
    }

    pub fn is_function_filter(&self) -> bool {
        matches!(self, UserFilter::Function(..))
    }

    pub fn from_args(args: &Args, local_krate: &Krate) -> Result<UserFilter, VirErr> {
        let validate_module_name = |s: &str| -> Result<vir::ast::Idents, VirErr> {
            let segments = parse_path_segments_from_user_str(s)?;
            if local_krate.modules.iter().find(|m| m.x.path.segments == segments).is_none() {
                let mut lines = local_krate
                    .modules
                    .iter()
                    .filter_map(|m| {
                        let name = module_name(&m.x.path);
                        (m.x.path.segments.len() > 0).then(|| format!("- {name}"))
                    })
                    .collect::<Vec<_>>();
                lines.sort(); // Present the available modules in sorted order
                let mut msg = vec![
                    format!(
                        "could not find module {s} specified by --verify-module or --verify-only-module"
                    ),
                    format!("available modules are:"),
                ];
                msg.extend(lines);
                msg.push(format!("or use --verify-root"));
                return Err(error(msg.join("\n")));
            }
            Ok(segments)
        };

        if !args.verify_function.is_empty() {
            assert!(!(args.verify_only_module.is_empty() && !args.verify_root));
            assert!(args.verify_module.is_empty());

            let mut modules: Vec<ModuleId> = Vec::new();
            for s in &args.verify_only_module {
                let module = validate_module_name(s)?;
                if !modules.contains(&module) {
                    modules.push(module);
                }
            }
            if args.verify_root && !modules.contains(&root_module_id()) {
                modules.push(root_module_id());
            }

            // Name each module's functions once, rather than once per pattern
            let module_fun_names: Vec<Vec<(Fun, String)>> = modules
                .iter()
                .map(|module| Self::module_fun_names(module, &local_krate.functions))
                .collect();
            // How a pattern names each module: `crate` for the root, else its path
            let qualifiers: Vec<String> = modules
                .iter()
                .map(
                    |m| if m.is_empty() { "crate".to_string() } else { module_name_of_segments(m) },
                )
                .collect();

            // Resolve every pattern before failing, so that one run reports all the bad ones
            let mut matches = HashSet::new();
            let mut errors = Vec::new();
            for func_name in &args.verify_function {
                match Self::get_matches(&qualifiers, &module_fun_names, func_name) {
                    Ok(m) => matches.extend(m),
                    Err(msg) => errors.push(msg),
                }
            }
            if !errors.is_empty() {
                return Err(error(errors.join("\n\n")));
            }
            return Ok(UserFilter::Function(modules, matches));
        }

        if args.verify_module.is_empty() && args.verify_only_module.is_empty() && !args.verify_root
        {
            return Ok(UserFilter::None);
        }

        let mut modules: Vec<ModuleId> = args
            .verify_module
            .iter()
            .map(|s| {
                let arg_segments = validate_module_name(s)?;
                let mods = local_krate
                    .modules
                    .iter()
                    .map(|m| m.x.path.segments.clone())
                    .filter(|m_segments| {
                        vir::ast_util::path_segments_match_prefix(m_segments, &arg_segments)
                    })
                    .collect::<Vec<ModuleId>>();
                Ok(mods)
            })
            .collect::<Result<Vec<Vec<ModuleId>>, VirErr>>()?
            .into_iter()
            .flatten()
            .collect();

        modules.extend(
            args.verify_only_module
                .iter()
                .map(|s| validate_module_name(s))
                .collect::<Result<Vec<ModuleId>, VirErr>>()?,
        );

        if args.verify_root {
            modules.push(root_module_id());
        }

        Ok(UserFilter::Modules(modules))
    }

    pub fn filter_modules(
        &self,
        modules: &Vec<vir::ast::Module>,
    ) -> Result<Vec<vir::ast::Module>, VirErr> {
        let mut remaining_modules: HashSet<&ModuleId> = match self {
            UserFilter::None => {
                return Ok(modules.clone());
            }
            UserFilter::Modules(m) => m.iter().collect(),
            UserFilter::Function(m, _) => m.iter().collect(),
        };

        let module_ids_to_verify = modules
            .iter()
            .filter(|m| {
                // Return true if the ModuleId is in the remaining_modules set,
                // and if so, remove it from the set.
                remaining_modules.take(&m.x.path.segments).is_some()
            })
            .cloned()
            .collect();

        assert!(remaining_modules.is_empty(), "Some modules were not found in the krate modules");

        Ok(module_ids_to_verify)
    }

    /// Filter the bucket list to only include buckets that contain some
    /// element accepted by the filter.
    /// Assumes the input vector is already restricted to the modules
    /// as returned by `filter_module_ids`.
    pub fn filter_buckets(&self, vec: Vec<(BucketId, Bucket)>) -> Vec<(BucketId, Bucket)> {
        match self {
            UserFilter::None | UserFilter::Modules(_) => vec,
            UserFilter::Function(..) => {
                vec.into_iter()
                    .filter(|(_, bucket)| {
                        // Check if any function in the bucket is accepted.
                        for fun in &bucket.funs {
                            if self.includes_function(fun) {
                                return true;
                            }
                        }
                        return false;
                    })
                    .collect()
            }
        }
    }

    /// The functions owned by the module, each with its name relative to the module.
    fn module_fun_names(module_id: &ModuleId, funs: &Vec<Function>) -> Vec<(Fun, String)> {
        funs.iter()
            .filter(|f| match &f.x.owning_module {
                None => false,
                Some(m) => module_id == &m.segments,
            })
            .map(|f| {
                let name = friendly_fun_name_crate_relative(
                    f.x.owning_module.as_ref().unwrap(),
                    &f.x.name,
                );
                (f.x.name.clone(), name)
            })
            .collect()
    }

    /// Get the functions that match the given pattern.
    ///
    /// The pattern is first matched as written, in all the selected modules.
    /// If that fails and the pattern starts with the name of a selected module
    /// (`foo::bar::f` or `crate::foo::bar::f`, or `crate::f` for the root module),
    /// the rest of the pattern is matched in that module only,
    /// trying the longest such module name first.
    ///
    /// Errors (with the message) if there is no match.
    fn get_matches(
        qualifiers: &[String],
        module_fun_names: &[Vec<(Fun, String)>],
        pattern: &String,
    ) -> Result<HashSet<Fun>, String> {
        let all_modules: Vec<usize> = (0..module_fun_names.len()).collect();
        let unqualified =
            Self::get_matches_in(qualifiers, module_fun_names, &all_modules, "", pattern, pattern);
        if unqualified.is_ok() {
            return unqualified;
        }
        let mut prefixes: Vec<(usize, String)> = qualifiers
            .iter()
            .enumerate()
            .flat_map(|(i, q)| {
                let absolute = (q != "crate").then(|| format!("crate::{q}::"));
                std::iter::once(format!("{q}::")).chain(absolute).map(move |p| (i, p))
            })
            .filter(|(_, p)| pattern.len() > p.len() && pattern.starts_with(p.as_str()))
            .collect();
        prefixes.sort_by_key(|(_, p)| std::cmp::Reverse(p.len()));
        let mut qualified_err = None;
        for (i, prefix) in prefixes {
            let function_pattern = &pattern[prefix.len()..];
            match Self::get_matches_in(
                qualifiers,
                module_fun_names,
                &[i],
                &prefix,
                pattern,
                function_pattern,
            ) {
                Ok(m) => return Ok(m),
                Err(msg) => {
                    qualified_err.get_or_insert(msg);
                }
            }
        }
        Err(qualified_err.unwrap_or_else(|| unqualified.unwrap_err()))
    }

    /// Get the functions in the given modules that match `function_pattern`,
    /// which is `pattern` without the module qualifier `prefix`.
    ///
    /// The first part of this process is to
    /// infer whether this is an "exact match" filter.
    /// (If the user doesn't supply any * in the pattern, then it is usuall
    /// exact - however, if there is no exact match, but there is _exactly one_
    /// partial match, then we upgrade to a partial match, i.e., return false)
    ///
    /// A wildcard pattern selects its matches in every module,
    /// but an exact name must not match in two modules.
    ///
    /// Errors (with the message) if there is no match.
    fn get_matches_in(
        qualifiers: &[String],
        module_fun_names: &[Vec<(Fun, String)>],
        modules: &[usize],
        prefix: &str,
        pattern: &str,
        function_pattern: &str,
    ) -> Result<HashSet<Fun>, String> {
        let several_modules = module_fun_names.len() > 1;
        let funs: Vec<(usize, &(Fun, String))> =
            modules.iter().flat_map(|&i| module_fun_names[i].iter().map(move |f| (i, f))).collect();
        // With several modules, show each function qualified by its module
        let display = |(i, (_, name)): &(usize, &(Fun, String))| {
            if several_modules { format!("{}::{name}", qualifiers[*i]) } else { name.clone() }
        };
        let display_sorted = |funs: &Vec<(usize, &(Fun, String))>| {
            let mut names = funs.iter().map(display).collect::<Vec<String>>();
            names.sort();
            names
        };

        // First, get the matches without doing anything fancy:
        // If the user provides a * pattern, then we filter according to the * pattern;
        // if the user provides an exact match (no *), then filter as an exact match.
        // If we find anything this way, we're done.
        let matches = Self::get_matches_strictly_by_pattern(function_pattern, &funs);
        let clean = function_pattern.trim_matches('*');
        if matches.len() > 0 {
            let first_module = matches[0].0;
            if clean == function_pattern && matches.iter().any(|(i, _)| *i != first_module) {
                let msg = vec![
                    format!(
                        "--verify-function {pattern} matches functions in more than one module, qualify it with the module (e.g. {}::{function_pattern}),",
                        qualifiers[first_module]
                    ),
                    format!("matched results are:"),
                ]
                .into_iter()
                .chain(display_sorted(&matches).iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(msg);
            }
            return Ok(matches.into_iter().map(|(_, f)| f.0.clone()).collect());
        }

        // Get all substring matches, even if the user didn't use any * in their pattern.
        // We might use of these automatically, or if not, this list will at least help us
        // print an informative error message.
        let substring_matches = Self::get_all_substring_matches(function_pattern, &funs);

        if clean == function_pattern {
            // If there's no exact match, but there is *exactly one* substring match,
            // then we go ahead and use that function.
            if substring_matches.len() == 1 {
                return Ok(substring_matches.iter().map(|f| f.1.0.clone()).collect());
            } else if substring_matches.len() > 1 {
                let msg = vec![
                    format!(
                        "more than one match found for --verify-function {pattern}, consider using wildcard {prefix}*{function_pattern}* to verify all matched results,"
                    ),
                    format!(
                        "or specify a unique substring for the desired function, matched results are:"
                    ),
                ].into_iter()
                .chain(display_sorted(&substring_matches).iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(msg);
            }
        } else {
            if substring_matches.len() >= 1 {
                let msg = vec![
                    format!("could not find function {pattern} specified by --verify-function,"),
                    format!("consider {prefix}*{clean}* if you want to verify similar functions:"),
                ]
                .into_iter()
                .chain(display_sorted(&substring_matches).iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(msg);
            }
        }

        // If there were absolutely no substring matches, then we fail by printing
        // out every possible function in the module.
        let msg = vec![
            format!("could not find function {pattern} specified by --verify-function"),
            format!("available functions are:"),
        ]
        .into_iter()
        .chain(display_sorted(&funs).iter().map(|f| format!("  - {f}")))
        .collect::<Vec<String>>()
        .join("\n");
        return Err(msg);
    }

    fn get_matches_strictly_by_pattern<'a>(
        function_pattern: &str,
        funs: &Vec<(usize, &'a (Fun, String))>,
    ) -> Vec<(usize, &'a (Fun, String))> {
        let clean = function_pattern.trim_matches('*');
        let left_wildcard = function_pattern.starts_with('*');
        let right_wildcard = function_pattern.ends_with('*');

        funs.iter()
            .filter(|(_, (_, name))| {
                if left_wildcard && !right_wildcard {
                    name.ends_with(clean)
                } else if !left_wildcard && right_wildcard {
                    name.starts_with(clean)
                } else if left_wildcard && right_wildcard {
                    name.contains(clean)
                } else {
                    name == clean
                }
            })
            .cloned()
            .collect()
    }

    fn get_all_substring_matches<'a>(
        function_pattern: &str,
        funs: &Vec<(usize, &'a (Fun, String))>,
    ) -> Vec<(usize, &'a (Fun, String))> {
        let clean = function_pattern.trim_matches('*');
        funs.iter().filter(|(_, (_, name))| name.contains(clean)).cloned().collect()
    }

    /// Check if the function is included in the filter.
    /// This assumes the function is already in the correct module
    /// (i.e., it only checks the function name).
    pub fn includes_function(&self, function_name: &Fun) -> bool {
        if let UserFilter::Function(_modules, matches) = self {
            matches.contains(function_name)
        } else {
            true
        }
    }
}
