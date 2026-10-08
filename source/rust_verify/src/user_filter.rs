use crate::buckets::{Bucket, BucketId};
use crate::config::Args;
use crate::util::error;
use crate::verifier::module_name;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{Fun, Function, Krate, VirErr};
use vir::ast_util::{
    fun_as_friendly_rust_name, parse_path_segments_from_user_str, path_as_friendly_rust_name,
};
use vir::def::krate_to_string_ignore_stable_id;

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
    /// The index of the function's module among the selected modules
    module: usize,
    /// The name relative to the function's module
    name: String,
    /// The names that a pattern with `::` is also matched against:
    /// the path from the crate root, if the function is named by a path in this crate,
    /// and the module's path followed by the relative name (without the crate's name),
    /// each with and without `crate::`
    qualified: Vec<String>,
    /// The name shown when several modules are selected
    listed: String,
    /// Where the function is defined, shown to tell apart functions listed by the same name
    location: String,
}

impl FunName {
    /// The names a pattern is matched against: the relative name,
    /// and if `qualified`, also the qualified names
    fn names(&self, qualified: bool) -> impl Iterator<Item = &str> {
        let qualified = if qualified { &self.qualified[..] } else { &[] };
        std::iter::once(self.name.as_str()).chain(qualified.iter().map(|n| n.as_str()))
    }

    fn display(&self, several_modules: bool) -> &str {
        if several_modules { &self.listed } else { &self.name }
    }
}

/// What a pattern selects, or why it selects nothing
enum Resolution<'a> {
    Selected(Vec<&'a FunName>),
    /// An exact pattern that matches functions in several modules
    Ambiguous(Vec<&'a FunName>),
    /// An exact pattern that matches no function, but is a substring of several
    Substrings(Vec<&'a FunName>),
    /// A wildcard pattern that matches no function, but whose `*`-less text is a substring of some
    Similar(Vec<&'a FunName>),
    NotFound,
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
            let several_modules = modules.len() > 1;

            // Resolve every pattern before failing, so that one run reports all the bad ones
            let mut matches = HashSet::new();
            let mut errors = Vec::new();
            let mut seen = HashSet::new();
            for pattern in args.verify_function.iter().filter(|p| seen.insert(p.as_str())) {
                match Self::resolve(&funs, pattern) {
                    Resolution::Selected(m) => matches.extend(m.iter().map(|f| f.fun.clone())),
                    failure => errors.push(Self::message(&funs, several_modules, pattern, failure)),
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
        // For each module: the prefix of the names of the functions in it, the prefix of the
        // names of the functions in the crate, and the module's path from the crate root
        // (empty for the root, otherwise ending with `::`)
        let mut prefixes: Vec<Option<(String, String, String)>> = vec![None; modules.len()];
        funs.iter()
            .filter_map(|f| {
                let owning_module = f.x.owning_module.as_ref()?;
                let module = modules.iter().position(|m| m == &owning_module.segments)?;
                let (module_prefix, krate_prefix, module_path) = prefixes[module]
                    .get_or_insert_with(|| {
                        let krate = krate_to_string_ignore_stable_id(&owning_module.krate);
                        let path = module_name(owning_module);
                        let path = if path.is_empty() { path } else { path + "::" };
                        (path_as_friendly_rust_name(owning_module) + "::", krate + "::", path)
                    });
                let full = fun_as_friendly_rust_name(&f.x.name);
                // A function may be named by a path outside its module
                // (e.g. a method of an impl of a type defined elsewhere);
                // then its relative name is its full name
                let name = full.strip_prefix(module_prefix.as_str()).unwrap_or(&full).to_string();
                let path = full.strip_prefix(krate_prefix.as_str());
                let owned = (!module_path.is_empty()).then(|| {
                    let rest = name.strip_prefix(krate_prefix.as_str()).unwrap_or(&name);
                    format!("{module_path}{rest}")
                });
                let mut qualified: Vec<String> = Vec::new();
                for n in path.into_iter().chain(owned.as_deref()) {
                    for n in [n.to_string(), format!("crate::{n}")] {
                        if !qualified.contains(&n) {
                            qualified.push(n);
                        }
                    }
                }
                let listed = match (path, &owned) {
                    (Some(p), _) if module_path.is_empty() => format!("crate::{p}"),
                    (Some(p), _) => p.to_string(),
                    (None, Some(owned)) => owned.clone(),
                    (None, None) => name.clone(),
                };
                // A span prints as `file:line:col: line:col (#ctxt)`
                let location = f.span.as_string.split(": ").next().unwrap_or("").to_string();
                Some(FunName { fun: f.x.name.clone(), module, name, qualified, listed, location })
            })
            .collect()
    }

    /// Resolve one pattern.
    ///
    /// A pattern is matched against each function's name relative to its module,
    /// and, if the pattern contains `::`, against its qualified names too.
    /// A pattern with `*` at either end selects every function with a name that it matches.
    /// A pattern without (an exact pattern) selects every function with a name equal to it,
    /// as long as these functions are all in one module (otherwise it is ambiguous).
    /// An exact pattern that equals no name selects the one function with a name that contains it,
    /// and is an error if several do.
    fn resolve<'a>(funs: &'a [FunName], pattern: &str) -> Resolution<'a> {
        let qualified = pattern.contains("::");
        let clean = pattern.trim_matches('*');
        let exact = clean == pattern;

        // First, get the matches without doing anything fancy:
        // If the user provides a * pattern, then we filter according to the * pattern;
        // if the user provides an exact match (no *), then filter as an exact match.
        // If we find anything this way, we're done.
        let matches: Vec<&FunName> = funs
            .iter()
            .filter(|f| f.names(qualified).any(|n| Self::matches_strictly_by_pattern(pattern, n)))
            .collect();
        if exact && matches.iter().any(|f| f.module != matches[0].module) {
            return Resolution::Ambiguous(matches);
        } else if matches.len() > 0 {
            return Resolution::Selected(matches);
        }

        // Get all substring matches, even if the user didn't use any * in their pattern.
        // We might use of these automatically, or if not, this list will at least help us
        // print an informative error message.
        // `*{clean}*` selects exactly these, by the same names.
        let substring_matches: Vec<&FunName> =
            funs.iter().filter(|f| f.names(qualified).any(|n| n.contains(clean))).collect();
        match (exact, substring_matches.len()) {
            (_, 0) => Resolution::NotFound,
            // If there's no exact match, but there is *exactly one* substring match,
            // then we go ahead and use that function.
            (true, 1) => Resolution::Selected(substring_matches),
            (true, _) => Resolution::Substrings(substring_matches),
            (false, _) => Resolution::Similar(substring_matches),
        }
    }

    /// The error message for a pattern that selects nothing
    fn message(
        funs: &[FunName],
        several_modules: bool,
        pattern: &str,
        failure: Resolution,
    ) -> String {
        // Sorted by name; with several modules, functions listed by the same name
        // are told apart by location, in the order they are defined
        let display_sorted = |mut funs: Vec<&FunName>| {
            let mut counts: HashMap<&str, usize> = HashMap::new();
            for f in &funs {
                *counts.entry(f.display(several_modules)).or_default() += 1;
            }
            funs.sort_by_key(|f| f.display(several_modules));
            funs.iter()
                .map(|f| {
                    let name = f.display(several_modules);
                    if several_modules && counts[name] > 1 {
                        format!("{name} (at {})", f.location)
                    } else {
                        name.to_string()
                    }
                })
                .collect::<Vec<_>>()
        };
        let clean = pattern.trim_matches('*');
        match failure {
            Resolution::Selected(_) => unreachable!(),
            Resolution::Ambiguous(matches) => {
                // Suggest a name of one of the matches that selects just that function,
                // or else one that selects just the matches in its module
                let selected = |name: &str| match Self::resolve(funs, name) {
                    Resolution::Selected(m) => Some(m),
                    _ => None,
                };
                let mut sorted = matches.clone();
                sorted.sort_by(|f, g| f.display(several_modules).cmp(g.display(several_modules)));
                let candidates = || {
                    sorted.iter().flat_map(|f| {
                        std::iter::once(f.display(several_modules))
                            .chain(f.qualified.iter().map(|n| n.as_str()))
                            .map(move |name| (*f, name))
                    })
                };
                let one_function = candidates().find(|(f, name)| {
                    selected(name).is_some_and(|m| m.len() == 1 && m[0].fun == f.fun)
                });
                let one_module = candidates().find(|(f, name)| {
                    selected(name).is_some_and(|m| {
                        let in_module = matches.iter().filter(|g| g.module == f.module);
                        m.len() == in_module.clone().count()
                            && in_module.zip(&m).all(|(g, h)| g.fun == h.fun)
                    })
                });
                let header = match (one_function, one_module) {
                    (Some((_, example)), _) => format!(
                        "--verify-function {pattern} matches more than one function, use a name that matches only one (e.g. {example}),"
                    ),
                    (None, Some((_, example))) => format!(
                        "--verify-function {pattern} matches functions in more than one module, use a name that matches the functions of only one module (e.g. {example}),"
                    ),
                    (None, None) => format!(
                        "--verify-function {pattern} matches functions in more than one module, and no name matches the functions of only one module,"
                    ),
                };
                Self::listing(
                    vec![header, format!("matched results are:")],
                    display_sorted(matches),
                )
            }
            Resolution::Substrings(matches) => Self::listing(
                vec![
                    format!(
                        "more than one match found for --verify-function {pattern}, consider using wildcard *{pattern}* to verify all matched results,"
                    ),
                    format!(
                        "or specify a unique substring for the desired function, matched results are:"
                    ),
                ],
                display_sorted(matches),
            ),
            Resolution::Similar(matches) => Self::listing(
                vec![
                    format!("could not find function {pattern} specified by --verify-function,"),
                    format!("consider *{clean}* if you want to verify similar functions:"),
                ],
                display_sorted(matches),
            ),
            // If there were absolutely no substring matches, then we fail by printing
            // out every possible function in the modules.
            Resolution::NotFound => Self::listing(
                vec![
                    format!("could not find function {pattern} specified by --verify-function"),
                    format!("available functions are:"),
                ],
                display_sorted(funs.iter().collect()),
            ),
        }
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
