use lalrpop_util::lalrpop_mod;
use std::io;
use crate::VAR_TABLE;
use crate::FUNC_TABLE;
use crate::PRIM_TABLE;
use crate::utils::ast::{Sentence, Var, Ident, Func};

lalrpop_mod!(parser);

pub fn get_token() -> Sentence{
    let mut input = String::new();

    loop{
        input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let res = parser::StmtParser::new().parse(&input).unwrap();

        match &res {
            Sentence::Primitive(prim) => {
                prim.print("it".to_string());
            },

            Sentence::PrimitiveAssignment(prim, id) => {
                let res = prim.print(id.to_string());
                unsafe {
                    PRIM_TABLE.insert(id.to_string(), res);
                }
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