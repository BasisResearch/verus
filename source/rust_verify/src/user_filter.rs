use crate::buckets::{Bucket, BucketId};
use crate::config::Args;
use crate::util::error;
use crate::verifier::module_name;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Fun, Function, Krate, VirErr};
use vir::ast_util::{
    friendly_fun_name_crate_relative, fun_as_friendly_rust_name, parse_path_segments_from_user_str,
    path_as_friendly_rust_name,
};

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

/// A function in one of the selected modules, with the names a pattern can match it by
struct FunName {
    fun: Fun,
    /// Index of the function's module among the selected modules
    module: usize,
    /// The name relative to the module, which an unqualified pattern matches
    name: String,
    /// The module qualifiers that a pattern can put before `name`
    /// (`foo::bar::` and `crate::foo::bar::`, or `crate::` for the root module);
    /// empty if `name` is not relative to the module
    qualifiers: Vec<String>,
}

impl FunName {
    /// The name qualified by its module, shown when several modules are selected
    fn qualified(&self) -> String {
        format!("{}{}", self.qualifiers.first().map_or("", |q| q.as_str()), self.name)
    }

    /// The name qualified by the path of its module from the crate root
    fn absolute(&self) -> String {
        format!("{}{}", self.qualifiers.last().map_or("", |q| q.as_str()), self.name)
    }

    /// The ways to read `pattern` for this function:
    /// as written (with qualifier ""), and without each qualifier it starts with.
    /// Each reading is (qualifier, pattern without the qualifier).
    fn readings<'p>(&self, pattern: &'p str, qualify: bool) -> Vec<(&str, &'p str)> {
        let qualified = self
            .qualifiers
            .iter()
            .filter(|q| qualify && pattern.len() > q.len() && pattern.starts_with(q.as_str()));
        std::iter::once(("", pattern))
            .chain(qualified.map(|q| (q.as_str(), &pattern[q.len()..])))
            .collect()
    }
}

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
            let funs = Self::fun_names(&modules, &local_krate.functions);

            // Resolve every pattern before failing, so that one run reports all the bad ones
            let mut matches = HashSet::new();
            let mut errors = Vec::new();
            for func_name in &args.verify_function {
                match Self::get_matches(&funs, modules.len() > 1, func_name) {
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

    /// The functions owned by the modules, each with the names a pattern can match it by.
    fn fun_names(modules: &[ModuleId], funs: &Vec<Function>) -> Vec<FunName> {
        funs.iter()
            .filter_map(|f| {
                let owning_module = f.x.owning_module.as_ref()?;
                let module = modules.iter().position(|m| m == &owning_module.segments)?;
                let name = friendly_fun_name_crate_relative(owning_module, &f.x.name);
                // Qualify with the module name that `name` was made relative to,
                // which starts with the crate's name, written `crate` in a pattern
                let qualifiers = if name == fun_as_friendly_rust_name(&f.x.name) {
                    vec![]
                } else {
                    match path_as_friendly_rust_name(owning_module).split_once("::") {
                        Some((_, relative)) => {
                            vec![format!("{relative}::"), format!("crate::{relative}::")]
                        }
                        None => vec!["crate::".to_string()],
                    }
                };
                Some(FunName { fun: f.x.name.clone(), module, name, qualifiers })
            })
            .collect()
    }

    /// Get the functions that match the given pattern.
    ///
    /// A pattern can be qualified by the module of the functions it names
    /// (`foo::bar::f` or `crate::foo::bar::f`, or `crate::f` for the root module).
    /// A function matches if the pattern, either as written or without its module qualifier,
    /// matches the function's name relative to its module; every reading takes part
    /// in each step of the search.
    ///
    /// With one module, the pattern is first matched only as written,
    /// as it was before qualifiers existed, so that such a pattern selects the same functions.
    ///
    /// Errors (with the message) if there is no match.
    fn get_matches(
        funs: &[FunName],
        several_modules: bool,
        pattern: &str,
    ) -> Result<HashSet<Fun>, String> {
        if !several_modules {
            if let Ok(matches) = Self::get_matches_in(funs, false, pattern, false) {
                return Ok(matches);
            }
        }
        Self::get_matches_in(funs, several_modules, pattern, true)
    }

    /// Get the functions that match `pattern`, read without a module qualifier
    /// unless `qualify` is set.
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
        funs: &[FunName],
        several_modules: bool,
        pattern: &str,
        qualify: bool,
    ) -> Result<HashSet<Fun>, String> {
        // With several modules, show each function qualified by its module
        let display = |f: &FunName| if several_modules { f.qualified() } else { f.name.clone() };
        let display_sorted = |funs: &Vec<&FunName>| {
            let mut names = funs.iter().map(|f| display(f)).collect::<Vec<String>>();
            names.sort();
            names
        };
        let exact = !pattern.contains('*');

        // First, get the matches without doing anything fancy:
        // If the user provides a * pattern, then we filter according to the * pattern;
        // if the user provides an exact match (no *), then filter as an exact match.
        // If we find anything this way, we're done.
        let matches: Vec<&FunName> = funs
            .iter()
            .filter(|f| {
                let readings = f.readings(pattern, qualify);
                readings.iter().any(|(_, p)| Self::matches_strictly_by_pattern(p, &f.name))
            })
            .collect();
        if matches.len() > 0 {
            if exact && matches.iter().any(|f| f.module != matches[0].module) {
                let first = matches.iter().min_by_key(|f| display(f)).unwrap();
                let example =
                    if display(first) == pattern { first.absolute() } else { display(first) };
                return Err(Self::listing(
                    vec![
                        format!(
                            "--verify-function {pattern} matches functions in more than one module, qualify it with the module (e.g. {example}),"
                        ),
                        format!("matched results are:"),
                    ],
                    display_sorted(&matches),
                ));
            }
            return Ok(matches.into_iter().map(|f| f.fun.clone()).collect());
        }

        // Get all substring matches, even if the user didn't use any * in their pattern.
        // We might use of these automatically, or if not, this list will at least help us
        // print an informative error message.
        // Each reading that matches suggests a wildcard pattern selecting its matches.
        let mut substring_matches: Vec<&FunName> = Vec::new();
        let mut wildcards: Vec<String> = Vec::new();
        for f in funs {
            let mut matched = false;
            for (qualifier, p) in f.readings(pattern, qualify) {
                let clean = p.trim_matches('*');
                if f.name.contains(clean) {
                    matched = true;
                    let wildcard = format!("{qualifier}*{clean}*");
                    if !wildcards.contains(&wildcard) {
                        wildcards.push(wildcard);
                    }
                }
            }
            if matched {
                substring_matches.push(f);
            }
        }
        let wildcards = wildcards.join(" and ");

        if exact {
            // If there's no exact match, but there is *exactly one* substring match,
            // then we go ahead and use that function.
            if substring_matches.len() == 1 {
                return Ok(substring_matches.iter().map(|f| f.fun.clone()).collect());
            } else if substring_matches.len() > 1 {
                let wildcard = if wildcards.contains(" and ") { "wildcards" } else { "wildcard" };
                return Err(Self::listing(
                    vec![
                        format!(
                            "more than one match found for --verify-function {pattern}, consider using {wildcard} {wildcards} to verify all matched results,"
                        ),
                        format!(
                            "or specify a unique substring for the desired function, matched results are:"
                        ),
                    ],
                    display_sorted(&substring_matches),
                ));
            }
        } else {
            if substring_matches.len() >= 1 {
                return Err(Self::listing(
                    vec![
                        format!(
                            "could not find function {pattern} specified by --verify-function,"
                        ),
                        format!("consider {wildcards} if you want to verify similar functions:"),
                    ],
                    display_sorted(&substring_matches),
                ));
            }
        }

        // If there were absolutely no substring matches, then we fail by printing
        // out every possible function in the module.
        Err(Self::listing(
            vec![
                format!("could not find function {pattern} specified by --verify-function"),
                format!("available functions are:"),
            ],
            display_sorted(&funs.iter().collect()),
        ))
    }

    /// An error message: the header lines, then one line per name
    fn listing(header: Vec<String>, names: Vec<String>) -> String {
        header
            .into_iter()
            .chain(names.iter().map(|f| format!("  - {f}")))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn matches_strictly_by_pattern(function_pattern: &str, name: &str) -> bool {
        let clean = function_pattern.trim_matches('*');
        let left_wildcard = function_pattern.starts_with('*');
        let right_wildcard = function_pattern.ends_with('*');

        if left_wildcard && !right_wildcard {
            name.ends_with(clean)
        } else if !left_wildcard && right_wildcard {
            name.starts_with(clean)
        } else if left_wildcard && right_wildcard {
            name.contains(clean)
        } else {
            name == clean
        }
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
