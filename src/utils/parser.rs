use lalrpop_util::lalrpop_mod;
use std::io;
use super::ast::{Sentence, Var, Ident};

lalrpop_mod!(parser);
static mut VAR_TABLE : Vec<Var> = Vec::new();

pub fn get_token() -> Sentence {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let res = parser::StmtParser::new().parse(&input).unwrap();

    match &res {
        Sentence::Assignment(id, expr) => {
            match id {
                Ident::Null => { expr.calculate().print(); },
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
                                value : expr.calculate(), 
                            };
                            VAR_TABLE[cnt].print();
                        }
                        else {
                            VAR_TABLE.push(Var{
                                name : name.to_string(), 
                                value : expr.calculate(), 
                            });
                            VAR_TABLE[VAR_TABLE.len() - 1].print();
                        }
                    }
                },
            }
        }
    }

    res
}