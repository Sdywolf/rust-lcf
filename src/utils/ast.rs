use crate::kernel::kernel::assume;
use crate::kernel::kernel::deduct_antysym_rule;
use crate::kernel::kernel::eq_mp;
use crate::kernel::kernel::inst_type;
use crate::kernel::kernel::mkComb;
use std::collections::HashMap;
use crate::VAR_TABLE;
use crate::FUNC_TABLE;
use crate::kernel::kernel::{Type, Term, refl, trans, abs, inst, beta, Thm};

#[derive(Clone, PartialEq, Eq)]
pub enum Constant {
    IntConst(i32),
    StrConst(String),
    BoolConst(bool),
    List(Vec<Constant>),
}
impl Constant {
    pub fn print(&self) {
        match &self {
            Constant::IntConst(val) => { println!("var it : int = {}", val); },
            Constant::StrConst(val) => { println!("var it : string = {}", val); },
            Constant::BoolConst(val) => { println!("var it : bool = {}", val); },
            Constant::List(list) => { 
                println!("var it : List, length = {}", list.len());
                for cons in list {
                    cons.print();
                }
            },
        };
    }
}

pub struct Func {
    pub name : String,
    pub args : Vec<String>,
    pub body : Box<Expr>,
}
impl Func {
    pub fn calculate(&self, arguments : Vec<Box<Expr> >) -> Constant {
        let mut res : Vec<Var> = Vec::new();
        let mut i = 0;
        while i < arguments.len() && i < self.args.len() {
            res.push(Var { name: self.args[i].clone(), value: arguments[i].calculate(&Vec::new()) });
            i = i + 1;
        }
        self.body.calculate(&res)
    }
}

// IdentList and IdentListNext are for the construction of functions' argtables in their definitions, like f(x, y, z).
pub struct IdentList {
    pub inside : String, 
    pub next : IdentListNext,
}
pub enum IdentListNext {
    Null,
    Cont(Box<IdentList>),
}

// ArgList and ArgListNext are for construction of functions' arglists, like f(1, 2, true).
pub struct ArgList {
    pub inside : Box<Expr>,
    pub next : ArgListNext,
}
pub enum ArgListNext {
    Null,
    Cont(Box<ArgList>),
}

// ListCstr and ListNext are for construction of List, like [1, 2, 3 + 4, 'asdf', true].
pub struct ListCstr {
    pub inside : Constant,
    pub next : ListNext,
}
pub enum ListNext {
    Null,
    Cont(Box<ListCstr>),
}

#[derive(Clone)]
pub enum Expr {
    Const(Constant),
    Id(String),
    Func(String, Vec< Box<Expr>>),
    Op(Box<Expr>, Opcode, Box<Expr>),
    Null,
}
impl Expr {
    pub fn calculate(&self, args : &Vec<Var>) -> Constant{
        match &self {
            Expr::Func(func_id, argtable) => {
                let mut res = Constant::BoolConst(true);

                unsafe {
                    let mut cnt = 0;
                    while cnt < FUNC_TABLE.len() {
                        if FUNC_TABLE[cnt].name == func_id.to_string() {
                            break;
                        }
                        cnt = cnt + 1;
                    }

                    if cnt == FUNC_TABLE.len() {
                        panic!("Function {} has not been defined!", func_id);
                    }

                    res = FUNC_TABLE[cnt].calculate(argtable.to_vec());                        
                }
                res
            },

            Expr::Id(id) => {
                let mut cnt = 0;
                let mut found = false;
                let mut res : Constant = Constant::BoolConst(true);
                while cnt < args.len() {
                    if args[cnt].name == id.to_string() {
                        found = true;
                        res = args[cnt].value.clone();
                        break;
                    }
                    cnt = cnt + 1;
                }
                if !found { unsafe {
                    cnt = 0;
                    while cnt < VAR_TABLE.len() {
                        if VAR_TABLE[cnt].name == id.to_string() {
                            res = VAR_TABLE[cnt].value.clone();
                            break;
                        }
                        cnt = cnt + 1;
                    }
                    if cnt == VAR_TABLE.len() {
                        panic!("No variable named {} is found.", id);
                    }
                } }
                res
            },

            Expr::Const(cons) => cons.clone(),

            Expr::Op(lhs, op, rhs) => {
                match op {
                    Opcode::OR => {
                        let mut res = false;
                        if let Constant::BoolConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"||\" found but LHS is not of type bool."); }

                        if let Constant::BoolConst(r) = rhs.calculate(args) { res = res || r; }
                        else { panic!("\"||\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::AND => {
                        let mut res = false;
                        if let Constant::BoolConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"&&\" found but LHS is not of type bool."); }

                        if let Constant::BoolConst(r) = rhs.calculate(args) { res = res && r; }
                        else { panic!("\"&&\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::NOT => {
                        let mut res = false;
                        if let Constant::BoolConst(r) = rhs.calculate(args) { res = !r; }
                        else { panic!("\"!\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::CAT => {
                        let mut res = String::new();
                        if let Constant::StrConst(l) = lhs.calculate(args) { res = l.clone(); }
                        else { panic!("\"^\" found but LHS is not of type string."); }

                        if let Constant::StrConst(r) = rhs.calculate(args) { 
                            res.remove(res.len() - 1);
                            let mut rr = r.clone();
                            rr.remove(0);
                            res = res + &rr;
                        }
                        else { panic!("\"^\" found but RHS is not of type string."); }

                        Constant::StrConst(res)
                    },

                    Opcode::ADD => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"+\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate(args) { res = res + r; }
                        else { panic!("\"+\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::SUB => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"-\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate(args) { res = res - r; }
                        else { panic!("\"-\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::MUL => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"*\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate(args) { res = res * r; }
                        else { panic!("\"*\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::DIV => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate(args) { res = l; }
                        else { panic!("\"/\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate(args) { res = res / r; }
                        else { panic!("\"/\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::LESS => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate(args) { l = ll; }
                        else { panic!("\"<\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate(args) { r = rr;}
                        else { panic!("\"<\" found but RHS is not of type int."); }

                        Constant::BoolConst(l < r)
                    },

                    Opcode::GREATER => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate(args) { l = ll; }
                        else { panic!("\">\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate(args) { r = rr;}
                        else { panic!("\">\" found but RHS is not of type int."); }

                        Constant::BoolConst(l > r)
                    },

                    Opcode::EQ => {
                        Constant::BoolConst(lhs.calculate(args) == rhs.calculate(args))
                    },

                    Opcode::UNEQ => {
                        Constant::BoolConst(lhs.calculate(args) != rhs.calculate(args))
                    },

                    Opcode::LEQ => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate(args) { l = ll; }
                        else { panic!("\"<=\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate(args) { r = rr;}
                        else { panic!("\"<=\" found but RHS is not of type int."); }

                        Constant::BoolConst(l <= r)
                    },

                    Opcode::GEQ => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate(args) { l = ll; }
                        else { panic!("\">=\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate(args) { r = rr;}
                        else { panic!("\">=\" found but RHS is not of type int."); }

                        Constant::BoolConst(l >= r)
                    },

                    _ => { panic!("Primitives haven't been implemented yet."); }
                }
            },
            _ => { panic!("Null expression has been met."); }
        }
    }
}

#[derive(Copy)]
pub enum Opcode {
    OR,
    AND,
    NOT,
    CAT,
    ADD,
    SUB,
    MUL,
    DIV,
    LESS,
    GREATER,
    EQ,
    UNEQ,
    LEQ,
    GEQ,
}
impl Clone for Opcode {
    fn clone(&self) -> Opcode {
        *self
    }
}

// primitives
pub enum PrimLaw {
    REFL, // term -> thm
    TRANS, // thm -> thm -> thm
    MK_COMB, // thm * thm -> thm
    ABS, // term -> thm -> thm
    BETA, // term -> term -> thm
    ASSUME, // term -> thm
    EQ_MP, // thm -> thm -> thm
    DEDUCT_ANTYSYM_RULE, // thm -> thm -> thm
    INST_TYPE, // (hol_type * hol_type) list -> thm -> thm
    INST, // (term * term) list -> thm -> thm
}

pub enum Prim {
    PrimTerm(Term),
    TypeList(HashMap<String, Type>),
    TermList(HashMap<String, Term>),
    PrimNode(PrimLaw, Box<Prim>, Box<Prim>),
    Null,
}
impl Prim{
    pub fn to_term(&self) -> &Term {
        match &self {
            Prim::PrimTerm(tm) => { println!("{}", tm); tm},
            _ => {
                panic!("This is not a term!");
            },
        }
    }

    pub fn to_typelist(&self) -> &HashMap<String, Type> {
        match &self {
            Prim::TypeList(tl) => tl,
            _ => {
                panic!("This is not a typelist!");
            },
        }
    }

    pub fn to_termlist(&self) -> &HashMap<String, Term> {
        match &self{
            Prim::TermList(tl) => tl,
            _ => {
                panic!("This is not a termlist!");
            },
        }
    }

    pub fn apply(&self) -> Thm {
        match &self {
            Prim::PrimNode(law, p1, p2) => {
                match *law {
                    PrimLaw::REFL => refl(p1.to_term()),
                    PrimLaw::TRANS => trans(&p1.apply(), &p2.apply()),
                    PrimLaw::MK_COMB => mkComb(&p1.apply(), &p2.apply()),
                    PrimLaw::ABS => abs(p1.to_term(), &p2.apply()),
                    PrimLaw::BETA => beta(p1.to_term(), p2.to_term()),
                    PrimLaw::ASSUME => assume(p1.to_term()),
                    PrimLaw::EQ_MP => eq_mp(&p1.apply(), &p2.apply()),
                    PrimLaw::DEDUCT_ANTYSYM_RULE => deduct_antysym_rule(&p1.apply(), &p2.apply()),
                    PrimLaw::INST => inst(p1.to_termlist(), &p2.apply()),
                    PrimLaw::INST_TYPE => inst_type(p1.to_typelist(), &p2.apply()),
                }
            },
            _ => { panic!("This is not a primitive."); },
        }
    }
}

pub struct TypeListConstructor {
    pub str : String,
    pub tp : Type,
    pub next : TypeListNext,
}

pub enum TypeListNext {
    Null,
    Cont(Box<TypeListConstructor>),
}

pub struct TermListConstructor {
    pub str : String,
    pub tm : Term,
    pub next : TermListNext,
}

pub enum TermListNext {
    Null,
    Cont(Box<TermListConstructor>),
}

pub enum Sentence {
    Assignment(Ident, Box<Expr>),
    FuncDef(String, Vec<String>, Box<Expr>),
    Primitive(Box<Prim>),
}

pub enum Ident {
    Name(String),
    Null,
}

pub struct Var {
    pub name : String,
    pub value : Constant,
}
impl Var {
    pub fn print(&self) {
        print!("var {} : ", self.name);
        match &self.value {
            Constant::IntConst(val) => { println!("int = {}", val); },
            Constant::StrConst(val) => { println!("string = {}", val); },
            Constant::BoolConst(val) => { println!("bool = {}", val); },
            Constant::List(list) => { 
                println!("List, length = {}", list.len());
                for cons in list {
                    cons.print();
                }
            },
        };
    }
}