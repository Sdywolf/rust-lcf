#[derive(Clone, PartialEq, Eq)]
pub enum Constant {
    IntConst(i32),
    StrConst(String),
    BoolConst(bool),
    Term(String),
}

impl Constant {
    pub fn print(&self) {
        print!("var it : ");
        match &self {
            Constant::IntConst(val) => { println!("int = {}", val); },
            Constant::StrConst(val) => { println!("string = {}", val); },
            Constant::BoolConst(val) => { println!("bool = {}", val); },
            Constant::Term(val) => { println!("term = {}", val);}
        };
    }

}

pub enum Expr {
    Const(Constant),
    Op(Box<Expr>, Opcode, Box<Expr>),
    Null,
}

impl Expr {
    pub fn calculate(&self) -> Constant{
        match &self {
            Expr::Const(cons) => cons.clone(),
            Expr::Op(lhs, op, rhs) => {
                match op {
                    Opcode::OR => {
                        let mut res = false;
                        if let Constant::BoolConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"||\" found but LHS is not of type bool."); }

                        if let Constant::BoolConst(r) = rhs.calculate() { res = res || r; }
                        else { panic!("\"||\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::AND => {
                        let mut res = false;
                        if let Constant::BoolConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"&&\" found but LHS is not of type bool."); }

                        if let Constant::BoolConst(r) = rhs.calculate() { res = res && r; }
                        else { panic!("\"&&\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::NOT => {
                        let mut res = false;
                        if let Constant::BoolConst(r) = rhs.calculate() { res = !r; }
                        else { panic!("\"!\" found but RHS is not of type bool."); }

                        Constant::BoolConst(res)
                    },

                    Opcode::CAT => {
                        let mut res = String::new();
                        if let Constant::StrConst(l) = lhs.calculate() { res = l.clone(); }
                        else { panic!("\"^\" found but LHS is not of type string."); }

                        if let Constant::StrConst(r) = rhs.calculate() { 
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
                        if let Constant::IntConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"+\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate() { res = res + r; }
                        else { panic!("\"+\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::SUB => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"-\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate() { res = res - r; }
                        else { panic!("\"-\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::MUL => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"*\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate() { res = res * r; }
                        else { panic!("\"*\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::DIV => {
                        let mut res = 0;
                        if let Constant::IntConst(l) = lhs.calculate() { res = l; }
                        else { panic!("\"/\" found but LHS is not of type int."); }

                        if let Constant::IntConst(r) = rhs.calculate() { res = res / r; }
                        else { panic!("\"/\" found but RHS is not of type int."); }

                        Constant::IntConst(res)
                    },

                    Opcode::LESS => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate() { l = ll; }
                        else { panic!("\"<\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate() { r = rr;}
                        else { panic!("\"<\" found but RHS is not of type int."); }

                        Constant::BoolConst(l < r)
                    },

                    Opcode::GREATER => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate() { l = ll; }
                        else { panic!("\">\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate() { r = rr;}
                        else { panic!("\">\" found but RHS is not of type int."); }

                        Constant::BoolConst(l > r)
                    },

                    Opcode::EQ => {
                        Constant::BoolConst(lhs.calculate() == rhs.calculate())
                    },

                    Opcode::UNEQ => {
                        Constant::BoolConst(lhs.calculate() != rhs.calculate())
                    },

                    Opcode::LEQ => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate() { l = ll; }
                        else { panic!("\"<=\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate() { r = rr;}
                        else { panic!("\"<=\" found but RHS is not of type int."); }

                        Constant::BoolConst(l <= r)
                    },

                    Opcode::GEQ => {
                        let mut l = 0;
                        let mut r = 0;
                        if let Constant::IntConst(ll) = lhs.calculate() { l = ll; }
                        else { panic!("\">=\" found but LHS is not of type int."); }

                        if let Constant::IntConst(rr) = rhs.calculate() { r = rr;}
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

    // primitives
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

pub enum Sentence {
    Assignment(Ident, Box<Expr>),
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
            Constant::Term(val) => {println!("term = {}", val); }
        };
    }
}