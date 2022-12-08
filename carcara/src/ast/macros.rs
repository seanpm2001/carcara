/// A macro to help pattern match terms.
///
/// Since a term holds references to its subterms in `Vec`s and `Rc`s, pattern matching a complex
/// term can be difficult and verbose. This macro helps with that. Given a term and a pattern with
/// which to match it, this macro will deconstruct the term and (if it matches the pattern) return
/// the subterms specified by the pattern.
///
/// The syntax to use this macro is `match_term!(<pattern> = <value>)`, where `<value>` is an
/// expression of type `Term` or `Rc<Term>`, and `<pattern>` is an s-expression that specifies the
/// pattern with which to match the given term. Free variables in the pattern will match any term,
/// and this term will be returned by the macro.
///
/// The return type of this macro is `Option<T>` where the exact structure of `T` will reflect the
/// pattern given. For example, `match_term!((and (= a b) c) = term)` will return an
/// `Option<((&Rc<Term>, &Rc<Term>), &Rc<Term>)>`. If the term does not match the pattern, the macro
/// returns `None`.
///
/// # Examples
///
/// Removing two leading negations from a term:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = TermPool::new();
/// # let t = build_term!(pool, (not (not {pool.bool_false()})));
/// let p = match_term!((not (not p)) = t).unwrap();
/// ```
///
/// Deconstructing complex nested terms:
/// ```
/// # use carcara::{ast::*, match_term, parser::*};
/// # pub fn parse_term(input: &str) -> Rc<Term> {
/// #     let mut pool = TermPool::new();
/// #     let mut parser = Parser::new(&mut pool, input.as_bytes(), true, false, false).unwrap();
/// #     parser.parse_term().unwrap()
/// # }
/// # let t = parse_term("(and (=> false false) (> (+ 0 0) 0))");
/// let ((p, q), ((a, b), c)) = match_term!((and (=> p q) (> (+ a b) c)) = t).unwrap();
/// ```
///
/// Pattern matching against boolean constants:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = TermPool::new();
/// # let t = build_term!(pool, (or {pool.bool_false()} {pool.bool_false()}));
/// let (p, ()) = match_term!((or p false) = t).unwrap();
/// ```
///
/// Pattern matching quantifier terms:
/// ```
/// # use carcara::{ast::*, match_term, parser::*};
/// # pub fn parse_term(input: &str) -> Rc<Term> {
/// #     let mut pool = TermPool::new();
/// #     let mut parser = Parser::new(&mut pool, input.as_bytes(), true, false, false).unwrap();
/// #     parser.parse_term().unwrap()
/// # }
/// # let t = parse_term("(forall ((x Int) (y Int)) (> x y))");
/// let (bindings, (x, y)) = match_term!((forall ... (> x y)) = t).unwrap();
/// ```
///
/// Pattern matching against a variable number of arguments:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = TermPool::new();
/// # let t = build_term!(pool, (and {pool.bool_false()} {pool.bool_false()}));
/// let args: &[Rc<Term>] = match_term!((and ...) = t).unwrap();
/// ```
#[macro_export]
macro_rules! match_term {
    (true = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_true() { Some(()) } else { None }
    };
    (false = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_false() { Some(()) } else { None }
    };
    ((forall ... $args:tt) = $var:expr) => {
        if let $crate::ast::Term::Quant($crate::ast::Quantifier::Forall, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            match_term!($args = inner).and_then(|inner| Some((bindings, inner)))
        } else {
            None
        }
    };
    ((exists ... $args:tt) = $var:expr) => {
        if let $crate::ast::Term::Quant($crate::ast::Quantifier::Exists, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            match_term!($args = inner).and_then(|inner| Some((bindings, inner)))
        } else {
            None
        }
    };
    ($bind:ident = $var:expr) => { Some($var) };
    (($op:tt $($args:tt)+) = $var:expr) => {{
        if let $crate::ast::Term::Op(match_term!(@GET_VARIANT $op), args) =
            &$var as &$crate::ast::Term
        {
            match_term!(@ARGS ($($args)+) = args.as_slice())
        } else {
            None
        }
    }};

    (@ARGS (...) = $var:expr) => { Some($var) };
    (@ARGS ($arg:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3) = $var)
    };
    (@ARGS_IDENT ( $($name:ident : $arg:tt),* ) = $var:expr) => {
        if let [$($name),*] = $var {
            #[allow(unused_parens)]
            #[allow(clippy::manual_map)]
            match ($(match_term!($arg = $name)),*) {
                ($(Some($name)),*) => Some(($($name),*)),
                _ => None,
            }
        } else {
            None
        }
    };
    (@GET_VARIANT not)      => { $crate::ast::Operator::Not };
    (@GET_VARIANT =>)       => { $crate::ast::Operator::Implies };
    (@GET_VARIANT and)      => { $crate::ast::Operator::And };
    (@GET_VARIANT or)       => { $crate::ast::Operator::Or };
    (@GET_VARIANT xor)      => { $crate::ast::Operator::Xor };
    (@GET_VARIANT =)        => { $crate::ast::Operator::Equals };
    (@GET_VARIANT distinct) => { $crate::ast::Operator::Distinct };
    (@GET_VARIANT ite)      => { $crate::ast::Operator::Ite };
    (@GET_VARIANT +)        => { $crate::ast::Operator::Add };
    (@GET_VARIANT -)        => { $crate::ast::Operator::Sub };
    (@GET_VARIANT *)        => { $crate::ast::Operator::Mult };
    (@GET_VARIANT div)      => { $crate::ast::Operator::IntDiv };
    (@GET_VARIANT /)        => { $crate::ast::Operator::RealDiv };
    (@GET_VARIANT <)        => { $crate::ast::Operator::LessThan };
    (@GET_VARIANT >)        => { $crate::ast::Operator::GreaterThan };
    (@GET_VARIANT <=)       => { $crate::ast::Operator::LessEq };
    (@GET_VARIANT >=)       => { $crate::ast::Operator::GreaterEq };
}

/// A variant of `match_term` that returns a `Result<_, CheckerError>` instead of an `Option`.
///
/// The error returned by this macro is always `CheckerError::TermOfWrongForm`.
#[macro_export]
macro_rules! match_term_err {
    ($pat:tt = $var:expr) => {{
        let var = $var;
        match_term!($pat = var).ok_or_else(|| {
            // Note: Annoyingly, the `stringify!` macro can't fully keep whitespace when turning a
            // token tree into a string. It will add spaces when they are required for the tokens
            // to make sense, but remove any other whitespace. This means that, for instance, the
            // token tree `(not (and ...))` will be stringified to `(not(and ...))`. One way to
            // solve this would be to create a procedural macro that uses the tokens `span` to
            // infer how many characters there were between each token, and assume they were all
            // spaces
            $crate::checker::error::CheckerError::TermOfWrongForm(stringify!($pat), var.clone())
        })
    }};
}

/// A macro to help build new terms.
///
/// This macro takes two arguments: the `TermPool` with which to build the term, and an s-expression
/// representing the term to be built. Subterms in that s-expression that are surrounded by `{}` are
/// evaluated as expressions, and they should have type `Rc<Term>`.
///
/// # Examples
///
/// Building the term `(and true (not false))`:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// let mut pool = TermPool::new();
/// let t = build_term!(pool, (and {pool.bool_true()} (not {pool.bool_false()})));
/// assert!(match_term!((and true (not false)) = t).is_some());
/// ```
#[macro_export]
macro_rules! build_term {
    ($pool:expr, {$terminal:expr}) => { $terminal };
    ($pool:expr, ($op:tt $($args:tt)+)) => {{
        let term = $crate::ast::Term::Op(
            match_term!(@GET_VARIANT $op),
            vec![ $(build_term!($pool, $args)),+ ],
        );
        $pool.add_term(term)
    }};
}

/// Helper macro to construct `Terminal` terms.
#[deprecated]
macro_rules! terminal {
    (int $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Integer($e.into()))
    };
    (real $num:literal / $denom:literal) => {{
        let num: rug::Integer = $num.into();
        let denom: rug::Integer = $denom.into();
        $crate::ast::Term::Terminal($crate::ast::Terminal::Real((num, denom).into()))
    }};
    (real $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Real($e))
    };
    (string $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::String($e.into()))
    };
    (var $e:expr ; $sort:ident) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Var(
            $crate::ast::Identifier::Simple($e.into()),
            $crate::ast::Term::$sort.clone().into()
        ))
    };
    (var $e:expr ; $sort:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Var(
            $crate::ast::Identifier::Simple($e.into()),
            $sort
        ))
    };
    (bool true) => {
        terminal!(
            var "true";
            $crate::ast::Rc::new($crate::ast::Term::Sort($crate::ast::Sort::Bool))
        )
    };
    (bool false) => {
        terminal!(
            var "false";
            $crate::ast::Rc::new($crate::ast::Term::Sort($crate::ast::Sort::Bool))
        )
    };
}

/// Implements `FromStr` and `Debug` for an enum, given a string representation for each variant.
macro_rules! impl_str_conversion_traits {
    ($enum_name:ident { $($variant:ident: $str:literal),* $(,)? }) => {
        impl std::str::FromStr for $enum_name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($str => Ok($enum_name::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for $enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let s = match self {
                    $($enum_name::$variant => $str,)*
                };
                write!(f, "{}", s)
            }
        }
    }
}

#[cfg(test)]
macro_rules! assert_deep_eq {
    ($($input:tt)*) => { assert!($crate::ast::deep_eq($($input)*)) };
}

#[cfg(test)]
macro_rules! assert_deep_eq_modulo_reordering {
    ($($input:tt)*) => { assert!($crate::ast::deep_eq_modulo_reordering($($input)*)) };
}

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::parser::tests::{parse_term, parse_terms};

    #[test]
    fn test_match_term() {
        let bool_sort = Rc::new(Term::Sort(Sort::Bool));
        let bool_false = Term::var("false", bool_sort.clone());
        let bool_true = Term::var("true", bool_sort);

        let term = parse_term("(= (= (not false) (= true false)) (not true))");
        let ((a, (b, c)), d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        assert_deep_eq!(a.as_ref(), &bool_false);
        assert_deep_eq!(b.as_ref(), &bool_true);
        assert_deep_eq!(c.as_ref(), &bool_false);
        assert_deep_eq!(d.as_ref(), &bool_true);

        let term = parse_term("(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        assert_deep_eq!(a.as_ref(), &bool_true);
        assert_deep_eq!(
            b.as_ref(),
            &Term::Op(
                Operator::Sub,
                vec![Rc::new(Term::integer(2)), Rc::new(Term::integer(2))],
            ),
        );
        assert_deep_eq!(
            c.as_ref(),
            &Term::Op(
                Operator::Mult,
                vec![Rc::new(Term::integer(1)), Rc::new(Term::integer(5))],
            ),
        );

        // Test the `...` pattern
        let term = parse_term("(not (and true false true))");
        match match_term!((not (and ...)) = &term) {
            Some([a, b, c]) => {
                assert_deep_eq!(&bool_true, a);
                assert_deep_eq!(&bool_false, b);
                assert_deep_eq!(&bool_true, c);
            }
            _ => panic!(),
        }
        let term = parse_term("(and (or false true) (= 2 2))");
        match match_term!((and (or ...) (= ...)) = &term) {
            Some(([a, b], [c, d])) => {
                assert_deep_eq!(&bool_false, a);
                assert_deep_eq!(&bool_true, b);
                assert_deep_eq!(&Term::integer(2), c);
                assert_deep_eq!(&Term::integer(2), d);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_build_term() {
        let definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ";
        let mut pool = TermPool::new();
        let bool_sort = pool.add_term(Term::Sort(Sort::Bool));
        let int_sort = pool.add_term(Term::Sort(Sort::Int));

        let (one, two, three) = (
            pool.add_term(Term::integer(1)),
            pool.add_term(Term::integer(2)),
            pool.add_term(Term::integer(3)),
        );
        let (a, b) = (
            pool.add_term(Term::var("a", int_sort.clone())),
            pool.add_term(Term::var("b", int_sort)),
        );
        let (p, q) = (
            pool.add_term(Term::var("p", bool_sort.clone())),
            pool.add_term(Term::var("q", bool_sort)),
        );
        let (r#true, r#false) = (pool.bool_true(), pool.bool_false());

        let cases = [
            ("(= a b)", build_term!(pool, (= {a} {b}))),
            (
                "(= 1 2)",
                build_term!(pool, (= {one.clone()} {two.clone()})),
            ),
            ("(not true)", build_term!(pool, (not {r#true.clone()}))),
            (
                "(or p false)",
                build_term!(pool, (or {p.clone()} {r#false.clone()})),
            ),
            (
                "(and (=> p q) (ite p false (= 1 3)))",
                build_term!(pool, (and
                    (=> {p.clone()} {q.clone()})
                    (ite {p.clone()} {r#false} (= {one.clone()} {three.clone()}))
                )),
            ),
            (
                "(distinct p q true)",
                build_term!(pool, (distinct {p} {q} {r#true})),
            ),
            (
                "(or (not (= 2 3)) (= 1 1))",
                build_term!(pool, (or
                    (not (= {two} {three}))
                    (= {one.clone()} {one})
                )),
            ),
        ];

        for (s, got) in &cases {
            let [expected] = parse_terms(definitions, [s]);
            assert_deep_eq!(&expected, got);
        }
    }
}
