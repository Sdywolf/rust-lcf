use std::io;
mod utils;
use utils::parser::get_token;
use utils::ast::{Sentence, Var, Ident};

static mut VAR_TABLE : Vec<Var> = Vec::new();

fn main() {
    loop{
        get_token();
    }
}
