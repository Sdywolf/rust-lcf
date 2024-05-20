use std::io;
mod kernel;
mod utils;
use utils::parser::get_token;
use utils::ast::{Sentence, Var, Ident};

static mut VAR_TABLE : Vec<Var> = Vec::new();

mod example {
    use super::kernel::kernel::{refl, trans, mkComb, abs, beta, assume, eq_mp, deduct_antysym_rule, inst_type, inst};
    use super::kernel::kernel::{Type, Term, Thm};
    use super::kernel::kernel::{aty, bool_ty};
    use std::collections::HashMap;
    use std::fmt;
    enum Prim {
        Refl(Term), // term -> thm
        Trans(Thm, Thm), // thm -> thm -> thm
        MkComb(Thm, Thm), // thm * thm -> thm
        Abs(Term, Thm), // term -> thm -> thm
        Beta(Term, Term), // term -> term -> thm
        Assume(Term), // term -> thm
        EqMP(Thm, Thm), // thm -> thm -> thm
        DeductAntySym(Thm, Thm), // thm -> thm -> thm
        InstType(HashMap<String, Type>, Thm), // (typevar * type) list -> thm -> thm
        Inst(HashMap<String, Term>, Thm), // (term * term) list -> thm -> thm
    }

    impl fmt::Display for Type {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Type::TyVar(name) => write!(f, "{}", name),
                Type::TyApp(t1, t2) => {
                    write!(f, "({}", t1)?;
                    for t in t2.iter() {
                        write!(f, " {}", t)?;
                    }
                    write!(f, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl fmt::Display for Term {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Term::Var(name, ty) => write!(f, "({} : {})", name, ty),
                Term::Const(name, ty) => write!(f, "({} : {})", name, ty),
                Term::Comb(t1, t2) => write!(f, "({} {})", t1, t2),
                Term::Abs(t1, t2) => write!(f, "(λ{}. {})", t1, t2),
            }
        }
    }

    impl fmt::Display for Thm {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Thm::Sequent(vs, t) => {
                    for v in vs.iter() {
                        write!(f, "{}; ", v)?;
                    }
                    write!(f, "|- {}", t)?;
                    Ok(())
                }
            }
        }
    }

    impl Prim {
        fn prim_apply(&self) -> Thm {
            match &self {
                Prim::Refl(t) => refl(t),
                Prim::Trans(t1, t2) => trans(t1, t2),
                Prim::MkComb(t1, t2) => mkComb(t1, t2),
                Prim::Abs(t1, t2) => abs(t1, t2),
                Prim::Beta(t1, t2) => beta(t1, t2),
                Prim::Assume(t) => assume(t),
                Prim::EqMP(t1, t2) => eq_mp(t1, t2),
                Prim::DeductAntySym(t1, t2) => deduct_antysym_rule(t1, t2),
                Prim::InstType(hm, t) => inst_type(hm, t),
                Prim::Inst(hm, t) => inst(hm, t)
            }
        }
    }

    pub fn example1() {
        let a = Term::Var("a".to_string(), aty());
        let refl_ex = Prim::Refl(a);
        println!("{}", refl_ex.prim_apply());
    }

    pub fn example2() {
        let a = Term::Var("a".to_string(), aty());
        let refl = Prim::Refl(a);
        let c = Term::Var("c".to_string(), aty());
        let abs = Prim::Abs(c, refl.prim_apply());
        println!("{}", abs.prim_apply());
    }

    pub fn example3() {
        let f = Term::Abs(Box::new(Term::Var("x".to_string(), aty())), Box::new(Term::Var("x".to_string(), aty())));
        let a = Term::Var("a".to_string(), aty());
        let comb = Term::Comb(Box::new(f), Box::new(a.clone()));
        let b = Term::Var("a".to_string(), aty());
        let abs = Term::Abs(Box::new(b.clone()), Box::new(comb.clone()));
        let c = Term::Var("a".to_string(), aty());
        let beta = Prim::Beta(abs, c);
        println!("{}", beta.prim_apply());
    }
}

fn main() {
    example::example1();
    example::example2();
    example::example3();
    
    // loop{
    //     let input = get_token();
    // }
}
