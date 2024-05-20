use crate::VAR_TABLE;
use crate::FUNC_TABLE;

#[derive(Clone, PartialEq, Eq)]
pub enum Constant {
    IntConst(i32),
    StrConst(String),
    BoolConst(bool),
    Term(String),
    List(Vec<Constant>),
}
impl Constant {
    pub fn print(&self) {
        match &self {
            Constant::IntConst(val) => { println!("var it : int = {}", val); },
            Constant::StrConst(val) => { println!("var it : string = {}", val); },
            Constant::BoolConst(val) => { println!("var it : bool = {}", val); },
            Constant::Term(val) => { println!("var it : term = {}", val);},
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
    BETA, // term -> thm
    ASSUME, // term -> thm
    EQ_MP, // thm -> thm -> thm
    DEDUCT_ANTYSYM_RULE, // thm -> thm -> thm
    INST_TYPE, // (hol_type * hol_type) list -> thm -> thm
    INST, // (term * term) list -> thm -> thm
}

pub enum PrimArg {
    Term(Constant),
    Id(String),
    Null,
}

pub struct PrimNode {
    pub law : PrimLaw,
    pub arg1 : PrimArg, 
    pub arg2 : PrimArg,
}

pub enum Sentence {
    Assignment(Ident, Box<Expr>),
    FuncDef(String, Vec<String>, Box<Expr>),
    Primitive(Ident, PrimNode),
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
            Constant::Term(val) => {println!("term = {}", val); },
            Constant::List(list) => { 
                println!("List, length = {}", list.len());
                for cons in list {
                    cons.print();
                }
            },
        };
    }
}