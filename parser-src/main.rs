use lalrpop_util::lalrpop_mod;
use std::io;
mod ast;
use crate::ast::{Sentence, Var, Ident, Func};

lalrpop_mod!(parser);

static mut VAR_TABLE : Vec<Var> = Vec::new();
static mut FUNC_TABLE : Vec<Func> = Vec::new();

fn main() {
    let mut input = String::new();

    loop{
        input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let res = parser::StmtParser::new().parse(&input).unwrap();

        match &res {
            Sentence::Primitive(id, node) => {
                // interact with the kernal
                println!("Relavent functions about primitives are in development.");
            },
            
            Sentence::FuncDef(func_id, arg_table, body) => {
                let mut cnt = 0;
                unsafe {
                    while cnt < FUNC_TABLE.len() {
                        if FUNC_TABLE[cnt].name == func_id.to_string() {
                            break;
                        }
                        cnt = cnt + 1;
                    }

                    if cnt < FUNC_TABLE.len() {
                        FUNC_TABLE.remove(cnt);
                    }
                    FUNC_TABLE.push(Func{ name : func_id.to_string(), args : arg_table.clone(), body : body.clone() });
                }
                println!("Defined function {}, with args number = {}.", func_id, arg_table.len());
            },

            Sentence::Assignment(id, expr) => {
                match id {
                    Ident::Null => { expr.calculate(&Vec::new()).print(); },
                    Ident::Name(name) => {
                        let mut cnt = 0;
                        unsafe {
                            while cnt < VAR_TABLE.len() {
                                if VAR_TABLE[cnt].name == *name {
                                    break;
                                }
                                cnt = cnt + 1;
                            }
                            
                            if cnt < VAR_TABLE.len() {
                                VAR_TABLE[cnt] = Var{
                                    name : name.to_string(), 
                                    value : expr.calculate(&Vec::new()), 
                                };
                                VAR_TABLE[cnt].print();
                            }
                            else {
                                VAR_TABLE.push(Var{
                                    name : name.to_string(), 
                                    value : expr.calculate(&Vec::new()), 
                                });
                                VAR_TABLE[VAR_TABLE.len() - 1].print();
                            }
                        }
                    },
                }
            },
        }
    }
}