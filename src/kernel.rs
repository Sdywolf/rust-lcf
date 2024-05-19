// Higher Order Logic (HOL) kernel

pub mod kernel {
    use lazy_static::lazy_static;
    use std::collections::HashMap;
    use core::panic;

    // The same type variable names in a Type are considered the same ocurrence
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    enum Type {
        TyVar(String),
        TyApp(String, Vec<Type>)
    }
    // impl Type {
    //     const BOOL_TY: Type = Type::TyApp(String::from("bool"), Vec::new());
    // }
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    enum Term {
        Var(String, Type),
        Const(String, Type),
        Comb(Box<Term>, Box<Term>),
        Abs(Box<Term>, Box<Term>)
    }
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    enum Thm {
        Sequent(Vec<Term>, Term)
    }
    struct TyTable {
        table : Vec<(String, i32)>
    }
    impl TyTable {
        fn is_in(&self, s : &String) -> bool {
            self.table.iter().any(|x| x.0 == *s)
        }

        fn new() -> TyTable {
            let mut table = TyTable {
                table: Vec::new()
            };
            table.init();
            table
        }
        fn types(&self) -> Vec<(String, i32)> {
            self.table.clone()
        }
        fn get_type_arity(&self, ty : &str) -> i32 {
            for i in self.table.iter() {
                if i.0 == ty {
                    return i.1;
                }
            }
            panic!("get_type_arity: not a type constant");
        }
        fn new_type(&mut self, name: &String, arity: i32) {
            if self.is_in(name) {
                panic!("new_type: type already defined");
            }
            self.table.push((name.clone(), arity));
        }
        fn init(&mut self) {
            self.new_type(&"bool".to_string(), 0);
            self.new_type(&"fun".to_string(), 2);
        }
    }
    fn make_ty(table: &TyTable, op: String, args: Vec<Type>) -> Type {
        let arity = table. get_type_arity(&op);
        if arity != args.len() as i32 {
            panic!("mk_type: wrong number of arguments");
        }
        Type::TyApp(op, args)
    }
    fn make_varty(name: String) -> Type {
        Type::TyVar(name)
    }
    fn dest_ty(ty: Type) -> (String, Vec<Type>) {
        match ty {
            Type::TyApp(op, args) => (op, args),
            _ => panic!("dest_ty: not a type application")
        }
    }
    fn dest_varty(ty: Type) -> String {
        match ty {
            Type::TyVar(name) => name,
            _ => panic!("dest_varty: not a type variable")
        }
    }
    fn is_ty(ty: Type) -> bool {
        match ty {
            Type::TyVar(_) => false,
            Type::TyApp(_, _) => true
        }
    }
    fn is_varty(ty: Type) -> bool {
        match ty {
            Type::TyVar(_) => true,
            Type::TyApp(_, _) => false
        }
    }
    fn get_ty_var(ty: &Type) -> Vec<String> {
        match ty {
            Type::TyVar(name) => vec![name.clone()],
            Type::TyApp(_, args) => args.iter().flat_map(|x| get_ty_var(x)).collect()
        }
    }
    fn type_subst(m: &HashMap<Type, Type>, ty: &Type) -> Type {
        match ty {
            Type::TyVar(_) => {
                match m.get(&ty) {
                    Some(t) => t.clone(),
                    None => ty.clone()
                }
            },
            Type::TyApp(op, args) => 
                Type::TyApp(op.clone(), args.iter().map(|x| type_subst(m, x)).collect())
        }
    }
    lazy_static! {
        static ref BOOL_TY: Type = Type::TyApp("bool".to_string(), Vec::new());
        static ref ATY: Type = Type::TyVar("A".to_string());
    }
    fn bool_ty() -> Type {
        BOOL_TY.clone()
    }
    fn aty() -> Type {
        ATY.clone()
    }
    struct TermTable {
        table: Vec<(String, Type)>
    }
    impl TermTable {
        fn is_in(&self, s: &String) -> bool {
            self.table.iter().any(|x| x.0 == *s)
        }
        fn new_term(&mut self, name: &String, ty: &Type) {
            if self.is_in(name) {
                panic!("new_term: term already defined");
            }
            self.table.push((name.clone(), ty.clone()));
        }
        fn init(&mut self) {
            self.new_term(&"=".to_string(), 
                &Type::TyApp("fun".to_string(), vec![aty(), Type::TyApp("fun".to_string(), vec![aty(), bool_ty()])]));
        }
        fn new() -> TermTable {
            let mut table = TermTable {
                table: Vec::new()
            };
            table.init();
            table
        }
        fn terms(&self) -> Vec<(String, Type)> {
            self.table.clone()
        }
        fn get_term_ty(&self, name: &String) -> Type {
            for i in self.table.iter() {
                if i.0 == *name {
                    return i.1.clone();
                }
            }
            panic!("get_term_type: term not found");
        }
    }

    /// type_of doesn't check the type consistency of argument t 
    fn type_of(t: &Term) -> Type {
        match t {
            Term::Var(_, ty) => ty.clone(),
            Term::Const(_, ty) => ty.clone(),
            Term::Comb(f, x) => {
                match type_of(f) {
                    Type::TyApp(name, args) => {
                        if name != "fun" || args.len() != 2 {
                            panic!("type_of: arrow type expected");
                        }
                        args[1].clone()
                    },
                    _ => panic!("type_of: arrow type expected")
                }
            },
            Term::Abs(v, t) => {
                let vty = type_of(v);
                let rty = type_of(t);
                Type::TyApp("fun".to_string(), vec![vty, rty])
            }
        }
    }
    fn is_var(t: &Term) -> bool {
        match t {
            Term::Var(_, _) => true,
            _ => false
        }
    }
    fn is_const(t: &Term) -> bool {
        match t {
            Term::Const(_, _) => true,
            _ => false
        }
    }
    fn is_comb(t: &Term) -> bool {
        match t {
            Term::Comb(_, _) => true,
            _ => false
        }
    }
    fn is_abs(t: &Term) -> bool {
        match t {
            Term::Abs(_, _) => true,
            _ => false
        }
    }
    fn make_var(name: &String, ty: &Type) -> Term {
        Term::Var(name.clone(), ty.clone())
    }
    fn make_const(name: &String, ty: &Type) -> Term {
        Term::Const(name.clone(), ty.clone())
    }
    fn make_comb(f: &Term, x: &Term) -> Term {
        Term::Comb(Box::new(f.clone()), Box::new(x.clone()))
    }
    fn make_abs(v: &Term, t: &Term) -> Term {
        Term::Abs(Box::new(v.clone()), Box::new(t.clone()))
    }
    fn dest_var(t: &Term) -> (String, Type) {
        match t {
            Term::Var(name, ty) => (name.clone(), ty.clone()),
            _ => panic!("dest_var: not a variable")
        }
    }
    fn dest_const(t: &Term) -> (String, Type) {
        match t {
            Term::Const(name, ty) => (name.clone(), ty.clone()),
            _ => panic!("dest_const: not a constant")
        }
    }
    fn dest_comb(t: &Term) -> (Term, Term) {
        match t {
            Term::Comb(f, x) => (*f.clone(), *x.clone()),
            _ => panic!("dest_comb: not a combination")
        }
    }
    fn dest_abs(t: &Term) -> (Term, Term) {
        match t {
            Term::Abs(v, t) => (*v.clone(), *t.clone()),
            _ => panic!("dest_abs: not an abstraction")
        }
    }
    /// Get free variables of t 
    fn frees(t: &Term) -> Vec<Term> {
        match t {
            Term::Var(_, _) => vec![t.clone()],
            Term::Const(_, _) => Vec::new(),
            Term::Comb(f, x) => {
                let mut fv = frees(f);
                fv.append(&mut frees(x));
                fv
            },
            Term::Abs(v, t) => {
                let mut fv = frees(t);
                fv.retain(|x| *x != **v);
                fv
            }
        }
    }
    /// Get all free variables of terms in ts 
    fn frees_list(ts: &Vec<Term>) -> Vec<Term> {
        ts.iter().fold(vec![], 
            |mut acc, x| {acc.append(&mut frees(x)); acc})
    }
    /// Check if all free variables in t are in ts
    fn frees_in(t: &Term, ts: &Vec<String>) -> bool {
        frees(t).iter().all(|x| match x {
            Term::Var(name, _) => ts.contains(name),
            _ => panic!("frees_in: frees returned list contains non variable")
        })
    }
    /// Check if any free varibale in t is in ts
    fn any_frees_in(t: &Term, ts: & Vec<String>) -> bool {
        frees(t).iter().any(|x| match x {
            Term::Var(name, _) => ts.contains(name),
            _ => panic!("any_frees_in: frees returned list contains non variable")
        })
    }
    /// Check if u is a free variable in t
    fn isfree_in(t: &Term, u: &Term) -> bool {
        frees(t).iter().any(|x| x == u)
    }

    /// Change variables in term t to avoid conflict with all
    /// free variables of every v in vs
    // fn var_name_prechange(t: &Term, vs: &Vec<String>) -> Term {
    //     if !frees(t).iter().any(|x| vs.contains(
    //         match x {
    //             Term::Var(name, _) => name,
    //             _ => panic!("bug discovered! var_name_prechange: frees(t) not a variable")
    //         }
    //     )) {
    //         return t.clone();
    //     } else {
    //         match t {
    //             Term::Var(name, ty) => {
    //                 let mut name1 = name.clone();
    //                 name1.push('\'');
    //                 while vs.iter().any(|x| *x == name1) {
    //                     name1.push('\'');
    //                 }
    //                 make_var(&name1, ty)
    //             },
    //             _ => panic!("var_name_prechange: not a variable")
    //         }
    //     }
    // }

    /// Variable substitution in term t; when apply substitution to an Abstraction, the
    /// renaming of bounded variables is a bit subtle;
    /// doesn't check type consistency of substitution
    fn var_subst(t: &Term, m: &mut HashMap<String, Term>) -> Term {
        /// env is a list of names of bounded variables that scope over t
        fn var_subst(t: &Term, env: &mut Vec<String>, m: &mut HashMap<String, Term>) -> Term {
            match t {
                Term::Var(name, _) => {
                    if env.iter().any(|x| *x == *name) {
                        t.clone()
                    } else {
                        match m.get(name) {
                            Some(x) => {
                                if any_frees_in(x, env) {
                                    panic!("var_subst: variable substitution not locally nameless")
                                }
                                x.clone()
                            },
                            None => t.clone()
                        }
                    }
                },
                Term::Const(_, _) => t.clone(),
                Term::Comb(f, x) => make_comb(&var_subst(f, env, m), &var_subst(x, env, m)),
                Term::Abs(v, tv) => {
                    match v.as_ref() {
                        Term::Var(name, ty) => {
                            env.push(name.clone());
                            let ret = make_abs(&v.clone(), &var_subst(tv, env, m));
                            env.pop();
                            ret
                        },
                        _ => panic!("var_subst: Abstracted term not a variable")
                    }
                }
            }
        }
        var_subst(t, &mut Vec::new(), m)
    }

    fn any_typevar_in(t: &Type, vs: &Vec<String>) -> bool {
        match t {
            Type::TyVar(name) => vs.contains(name),
            Type::TyApp(_, args) => args.iter().any(|x| any_typevar_in(x, vs))
        }
    }

    /// Substitute type variables in term t
    fn inst_term_type(t: &Term, m: &HashMap<String, Type>) -> Term {
        /// Get type variables of term t
        fn get_term_tyvar(t: &Term) -> Vec<String> {
            match t {
                Term::Var(_, ty) => get_ty_var(ty),
                Term::Const(_, ty) => get_ty_var(ty),
                Term::Comb(f, x) => {
                    let mut tv = get_term_tyvar(f);
                    tv.append(&mut get_term_tyvar(x));
                    tv
                },
                Term::Abs(v, t) => {
                    let mut tv = get_term_tyvar(v);
                    tv.append(&mut get_term_tyvar(t));
                    tv
                }
            }
        }
        fn inst_type(t: &Type, env: &Vec<String>, m: &HashMap<String, Type>) -> Type {
            match t {
                Type::TyVar(name) => {
                    if env.iter().any(|x| *x == *name) {
                        t.clone()
                    } else {
                        match m.get(name) {
                            Some(x) => {
                                if any_typevar_in(x, env) {
                                    panic!("inst_type: type substitution substs a type variable with a type that has a captured type variable name")
                                }
                                x.clone()
                            },
                            None => t.clone()
                        }
                    }
                },
                Type::TyApp(op, args) => {
                    Type::TyApp(op.clone(), args.iter().map(|x| inst_type(x, env, m)).collect())
                }
            
            }
        }
        fn inst_term_type(t: &Term, env: &mut Vec<String>, m: &HashMap<String, Type>) -> Term {
            match t {
                Term::Var(name, ty) => {
                    make_var(name, &inst_type(ty, env, m))
                },
                Term::Const(_, _) => t.clone(),
                Term::Comb(f, x) => make_comb(&inst_term_type(f, env, m), &inst_term_type(x, env, m)),
                Term::Abs(v, tv) => {
                    match v.as_ref() {
                        Term::Var(name, ty) => {
                            let mut num = 0;
                            for i in get_term_tyvar(v) {
                                env.push(i.clone());
                                num += 1;
                            }
                            let ret = make_abs(&v.clone(), &inst_term_type(tv, env, m));
                            while num > 0 {
                                env.pop();
                                num -= 1;
                            }
                            ret
                        },
                        _ => panic!("inst_type: Abstracted term not a variable")
                    }
                }
            }
        }
        inst_term_type(t, &mut Vec::new(), m)
    }

    /// Get the rator of a combination term
    fn rator(t: &Term) -> Term {
        match t {
            Term::Comb(f, _) => *f.clone(),
            _ => panic!("rator: not a combination")
        }
    }

    /// Get the rand of a combination term
    fn rand(t: &Term) -> Term {
        match t {
            Term::Comb(_, x) => *x.clone(),
            _ => panic!("rand: not a combination")
        }
    }

    /// Make a term list that is the union of two term lists;
    /// term_union doesn't remove duplicates
    fn term_union(l1: &Vec<Term>, l2: &Vec<Term>) -> Vec<Term> {
        let mut l = l1.clone();
        l.extend(l2.clone());
        l
    }

    /// Remove term t from term list l, result in a new term list
    fn term_remove(t: &Term, l: &Vec<Term>) -> Vec<Term> {
        l.iter().filter(|x| *x != t).cloned().collect()
    }

    /// Make a term representing the equality of two terms;
    /// type of "=" must be curried;
    /// the result term is Comb(Comb((=, TyApp(fun, [ty, Tyapp(fun, [ty, bool])])), l), r)
    fn safe_make_eq(l: &Term, r: &Term) -> Term {
        let ty = type_of(l);
        Term::Comb(
            Box::new(
                Term::Comb(
                    Box::new(Term::Const(
                        "=".to_string(),
                        Type::TyApp("fun".to_string(), vec![ty.clone(), Type::TyApp("fun".to_string(), vec![ty.clone(), bool_ty()])])
                    )), 
                    Box::new(l.clone())
                )
            ),
            Box::new(r.clone())
        )
    }

    /// Get the left and right terms of an equality term;
    /// only check that the typeapp name of the rator of l is "=";
    fn dest_eq(t: &Term) -> (Term, Term) {
        match t {
            Term::Comb(f, x) => {
                let r = x.clone();
                let l = match f.as_ref() {
                    Term::Comb(f1, x1) => {
                        if let Term::Const(name, _) = f1.as_ref() {
                            if name == "=" {
                                x1.clone()
                            } else {
                                panic!("dest_eq: not an equality")
                            }
                        } else {
                            panic!("dest_eq: not an equality")
                        }
                    },
                    _ => panic!("dest_eq: not an equality")
                };
                (*l, *r)
            },
            _ => panic!("dest_eq: not an equality")
        }
    }

    /// Get the hypotheses and conclusion of a theorem
    fn dest_thm(t: &Thm) -> (Vec<Term>, Term) {
        match t {
            Thm::Sequent(hyps, conc) => (hyps.clone(), conc.clone())
        }
    }

    fn hyps(t: &Thm) -> Vec<Term> {
        dest_thm(t).0.clone()
    }

    fn conc(t: &Thm) -> Term {
        dest_thm(t).1.clone()
    }

    /// Primitives for equalities:
    
    fn REFL(t: &Term) -> Thm {
        Thm::Sequent(vec![], safe_make_eq(t, t))
    }

    fn TRANS(t1: &Thm, t2: &Thm) -> Thm{
        let (hyps1, conc1) = dest_thm(t1);
        let (hyps2, conc2) = dest_thm(t2);
        let (l1, _) = dest_eq(&conc1);
        let (_, r2) = dest_eq(&conc2);
        Thm::Sequent(term_union(&hyps1, &hyps2) , safe_make_eq(&l1, &r2))
    }

    fn MK_COMB(l: &Thm, r: &Thm) -> Thm {
        let (hyps1, conc1) = dest_thm(l);
        let (hyps2, conc2) = dest_thm(r);
        let (l1, r1) = dest_eq(&conc1);
        let (l2, r2) = dest_eq(&conc2);
        Thm::Sequent(term_union(&hyps1, &hyps2), safe_make_eq(&make_comb(&l1, &l2), &make_comb(&r1, &r2)))
    }

    fn ABS(v: &Term, t: &Thm) -> Thm {
        match v {
            Term::Var(name, _) => {
                let (hyps, conc) = dest_thm(t);
                let (l, r) = dest_eq(&conc);
                if isfree_in(&l, v) || isfree_in(&r, v) {
                    panic!("ABS: variable free in term")
                }
                let l1 = make_abs(v, &l);
                let r1 = make_abs(v, &r);
                Thm::Sequent(hyps, safe_make_eq(&l1, &r1))
            },
            _ => panic!("ABS: v is not a variable")
        }
    }

    /// Primitives for lambda calculus:
    
    fn BETA(t: &Term, v: &Term) -> Thm {
        match t {
            Term::Abs(v0, t0) => {
                if v0.as_ref() == v {
                    Thm::Sequent(vec![], safe_make_eq(&t, t0.as_ref()))
                } else {
                    panic!("BETA: not a trivial BETA redex")
                }
            }, 
            _ => panic!("BETA: not an abstraction")
        }
    }

    /// Primitives for deduction:
    
    /// ASSUME: add a proposition to the hypotheses
    fn ASSUME(t: &Term) -> Thm {
        if type_of(t) == *BOOL_TY {Thm::Sequent(vec![t.clone()], t.clone())}
        else {panic!("ASSUME: not a proposition")}
    }
    /// EQ_MP: modus ponens for equalities
    fn EQ_MP(t1: &Thm, t2: &Thm) -> Thm {
        let (hyps1, conc1) = dest_thm(t1);
        let (hyps2, conc2) = dest_thm(t2);
        let (l1, r1) = dest_eq(&conc1);
        if l1 == conc2 {
            Thm::Sequent(term_union(&hyps1, &hyps2), r1)
        } else {
            panic!("EQ_MP: not a valid modus ponens")
        }
    }

    /// DEDUCT_ANTISYM_RULE: if conc1 and conc2 can imply each other, then they are equal
    fn DEDUCT_ANTYSYM_RULE(t1: &Thm, t2: &Thm) -> Thm {
        let (hyps1, conc1) = dest_thm(t1);
        let (hyps2, conc2) = dest_thm(t2);
        Thm::Sequent(term_union(&term_remove(&conc2, &hyps1), &term_remove(&conc1, &hyps2)), 
            safe_make_eq(&conc1, &conc2))
    }

    /// INST_TYPE: instantiate type variables in a theorem
    fn INST_TYPE(m: &HashMap<String, Type>, t: &Thm) -> Thm {
        fn term_inst_type_map(m: &HashMap<String, Type>, ts: &Vec<Term>) -> Vec<Term> {
            ts.iter().map(|x| inst_term_type(x, m)).collect()
        }
        match t {
            Thm::Sequent(hyps, conc) => {
                Thm::Sequent(term_inst_type_map(m, hyps), inst_term_type(conc, m))
            }
        }
    }

    /// INST: instantiate variables in a theorem
    fn INST(m: &HashMap<String, Term>, t: &Thm) -> Thm {
        fn term_inst_map(m: &HashMap<String, Term>, ts: &Vec<Term>) -> Vec<Term> {
            ts.iter().map(|x| var_subst(x, &mut m.clone())).collect()
        }
        match t {
            Thm::Sequent(hyps, conc) => {
                Thm::Sequent(term_inst_map(m, hyps), var_subst(conc, &mut m.clone()))
            }
        }
    }

    // / Primitives for axiom:
    
    // fn AXIOM(t: &Term) -> Thm {
    //     if type_of(t) == *BOOL_TY {
    //         Thm::Sequent(vec![t.clone()], t.clone())
    //     } else {
    //         panic!("AXIOM: not a proposition")
    //     }
    // }
}