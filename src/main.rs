#![feature(if_let_guard)]
#![feature(box_syntax)]
#![feature(box_patterns)]

use std::fmt::{Debug, Formatter, Display, self};
use std::collections::HashMap;
use std::io::{stdin, stdout, Write};
use SExp::*;
use Func::*;
use Env::*;
use ParserResult::*;

#[derive(Debug, Clone, PartialEq, Eq)]
enum SExp {
    Nil,
    Atom(String),
    Cons(Box<SExp>, Box<SExp>),
}

impl SExp {
    fn fst(self) -> SExp {
        match self {
            Cons(box lhs, _) => lhs,
            _                => Nil
        }
    }

    fn rst(self) -> SExp {
        match self {
            Cons(_, box rhs) => rhs,
            _                => Nil
        }
    }

    fn is_flat_list(self) -> bool {
        match self {
            Nil => true,
            Cons(box Atom(..), box rhs) => rhs.is_flat_list(),
            _                       => false
        }
    }

    fn to_flat_list(mut self) -> Result<Vec<String>, String> {
        let mut list = Vec::new();
        while let Cons(box Atom(name), box rhs) = self {
            list.push(name);
            self = rhs;
        }
        match self {
            Nil => Ok(list),
            _   => Err("Not a flat list!".into())
        }
    }

    fn to_list(mut self) -> Result<Vec<SExp>, String> {
        let mut list = Vec::new();
        while let Cons(box exp, box rhs) = self {
            list.push(exp);
            self = rhs;
        }
        Ok(list)
    }
}

impl Display for SExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let repr = match self {
            Nil            => "()".into(),
            Atom(name)     => format!("{}", name.clone()),
            Cons(box lhs, box rhs) => {
                let mut repr1 = String::from("(");
                repr1.push_str(&format!("{}", lhs));
                let mut rhsm = rhs.clone();
                loop {
                    match rhsm.clone() {
                        Cons(box rlhs, box rrhs) => {
                            repr1.push_str(&format!(" {}", rlhs));
                            rhsm = rrhs.clone();
                        },
                        Atom(atm)        => {
                            repr1.push_str(&format!("{})", atm));
                            break;
                            // panic!("Atom in the right of a Cons shouldn't happen! {}", atm)
                        },
                        Nil              => {
                            repr1.push_str(")");
                            break;
                        }
                    }
                }
                repr1
            },
        };
        write!(f, "{}", repr)
    }
}

#[derive(Debug, Clone)]
enum Func {
    IdF(SExp),
    CarF(Box<Func>),
    CdrF(Box<Func>),
    QuoteF(Box<Func>),
    AtomF(Box<Func>),
    ConsF(Box<Func>, Box<Func>),
    EqF(Box<Func>, Box<Func>),
    DefF(String, Box<Func>),
    LambdaD(Vec<String>, Box<Func>),
    LambdaF(Vec<String>, Box<Func>),
    LambdaA(Box<Func>, Vec<Func>),
    CustomF(String, Vec<Func>),
    CondF(Vec<(Func, Func)>),
    NullF(Box<Func>)
}

impl Display for Func {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let repr = match self {
            IdF(exp)           => format!("{}", exp),
            CarF(exp)          => format!("(CAR {})", exp),
            CdrF(exp)          => format!("(CDR {})", exp),
            ConsF(exp1, exp2)  => format!("(CONS {} {})", exp1, exp2),
            QuoteF(exp)        => format!("(QUOTE {})", exp),
            EqF(exp1, exp2)    => format!("(EQ {} {})", exp1, exp2),
            AtomF(exp)         => format!("(ATOM {})", exp),
            DefF(nm, exp)      => format!("({} {})", nm, exp),
            LambdaD(args, _)   => format!("(LAMBDA {:?})", args),
            LambdaF(args, _)   => format!("(LAMBDA {:?})", args),
            LambdaA(..)        => format!("(LAMBDA APPL)"),
            CustomF(nm, _)     => format!("{}", nm),
            CondF(pairs)       => {
                let mut repr1 = String::from("(COND");
                for (exp1, exp2) in pairs {
                    repr1.push_str(&format!(" ({} => {})", exp1, exp2));
                }
                repr1.push(')');
                repr1
            },
            NullF(exp)         => format!("(NULL {})", exp)
        };
        write!(f, "{}", repr)
    }
}

#[derive(Clone, Debug)]
enum Env {
    GCtx(HashMap<String, Func>),
    LCtx(HashMap<String, Func>, Box<Env>)
}

impl Env {
    fn new() -> Self {
        GCtx(HashMap::new())
    }

    fn lookup_var(&self, var: &str) -> Result<Func, String> {
        match self {
            GCtx(map)       => map.get(var).cloned().ok_or(format!("No such variable exists! '{}'", var)),
            LCtx(map, prnt) => match map.get(var).cloned() {
                Some(fnc)   => Ok(fnc),
                _           => prnt.lookup_var(var)
            }
        }
    }

    fn parse_func(&self, exp: SExp) -> Result<Func, String> {
        let result = Ok(match exp.clone() {
            Cons(box Atom(name), box args) => match name.as_str() {
                "CAR" => CarF(box self.parse_func(args.fst())?),
                "CDR" => CdrF(box self.parse_func(args.fst())?),
                "QUOTE" => QuoteF(box IdF(args.fst())),
                "ATOM" => AtomF(box self.parse_func(args.fst())?),
                "CONS"   => ConsF(box self.parse_func(args.clone().fst())?, box self.parse_func(args.rst().fst())?),
                "EQ"     => EqF(box self.parse_func(args.clone().fst())?, box self.parse_func(args.rst().fst())?),
                "DEF"    => match (args.clone().fst(), args.rst().fst()) {
                    (Atom(nm), rlhs) => DefF(nm, box self.parse_func(rlhs)?),
                    (other, _)       => Err(format!("First argument of a DEF has to be an Atom not '{}'", other))?
                },
                "LAMBDA" => match args.clone().fst().is_flat_list() {
                    true  => LambdaD(args.clone().fst().to_flat_list()?,
                                    box self.parse_func(args.rst().fst())?),
                    false => Err(format!("Lambda requires a list of arguments as it's first argument!"))?
                },
                "COND" => {
                    let mut pairs = Vec::new();
                    for arg in args.to_list()? {
                        let lhs = self.parse_func(arg.clone().fst())?;
                        let rhs = self.parse_func(arg.rst().fst())?;
                        pairs.push((lhs, rhs));
                    }
                    CondF(pairs)
                },
                "NULL" => NullF(box self.parse_func(args.fst())?),
                x if x.starts_with("C")
                    && x.ends_with("R")
                    && x.strip_prefix("C")
                        .unwrap()
                        .strip_suffix("R")
                        .unwrap()
                        .chars()
                        .all(|ch| ch == 'A' || ch == 'D') => {
                    let mut fnc = self.parse_func(args.fst())?;
                    for ch in x.strip_prefix("C").unwrap().strip_suffix("R").unwrap().chars().rev() {
                        fnc = match ch {
                            'A' => CarF(box fnc),
                            'D' => CdrF(box fnc),
                            _   => Err("This error will never be thrown!")?
                        }
                    }
                    fnc
                },
                _ => CustomF(name, args
                                .to_list()?
                                .iter()
                                .map(|xp| self.parse_func((*xp).clone()).unwrap())
                                .collect())
            },
            Cons(box exp, box args) => match self.parse_func(exp.clone())? {
                LambdaD(pars, func) => LambdaA(box LambdaF(pars, func), args
                            .to_list()?
                            .iter()
                            .map(|xp| self.parse_func((*xp).clone()).unwrap())
                            .collect()),
                _                  => Err(format!("Invalid function! {}", exp))?
            },
            atom@Atom(..) => IdF(atom),
            other => Err(format!("Invalid Function! {}", other))?
        });
        // println!("Parse {:?} = {:?}", exp, result);
        result
    }

    fn run_func(&mut self, func: Func) -> Result<SExp, String> {
        let result = Ok(
            match func.clone() {
                CarF(box exp) => self.run_func(exp)?.fst(),
                CdrF(box exp) => self.run_func(exp)?.rst(),
                QuoteF(box exp) => match exp {
                    IdF(exp) => exp,
                    other    => Err(format!("Func call: How did '{}' get here!?", other))?
                },
                ConsF(box fn1, box fn2)   => match (self.run_func(fn1)?, self.run_func(fn2)?) {
                    (atom1@Atom(_), atom2@Atom(_)) => Cons(box atom1, box Cons(box atom2, box Nil)),
                    (exp1, exp2)                   => Cons(box exp1, box exp2)
                },
                EqF(box lhs, box rhs)     => match (self.run_func(lhs)?, self.run_func(rhs)?) {
                    (Nil,       Nil)                     => Atom("T".into()),
                    (Atom(nm1), Atom(nm2)) if nm1 == nm2 => Atom("T".into()),
                    _                                    => Atom("F".into())
                },
                // AtomF(box IdF(Atom(nm))) => match self.lookup_var(&nm)? {
                    // IdF(Atom(..)) => Atom("T".into()),
                    // _             => Atom("F".into())
                // },
                AtomF(box fnc)               => match self.run_func(fnc)? {
                    Nil | Atom(..) => Atom("T".into()),
                    _              => Atom("F".into())
                },
                IdF(Atom(nm))            => self.run_func(self.lookup_var(&nm)?.clone())?,
                IdF(exp)                 => exp,
                DefF(nm, box IdF(Atom(nm2))) if nm == nm2 => Atom(nm),
                DefF(nm, box func)       => {
                    self.add_var(nm.clone(), func);
                    Atom(nm)
                },
                LambdaD(..) => {
                    Atom("LAMBDA".into())
                },
                LambdaF(_, box func)  => {
                    self.run_func(func)?
                },
                LambdaA(box LambdaF(pars, box func), args) => {
                    if pars.len() != args.len() {
                        Err("Invalid number of arguments provided to LAMBDA!")?;
                    }
                    let mut evld_args = Vec::new();
                    for arg in args {
                        let exp = self.run_func(arg)?;
                        evld_args.push(QuoteF(box IdF(exp)));
                    }
                    self.strt_ctx();
                    for (par, arg) in pars.iter().zip(evld_args) {
                        self.run_func(DefF(par.clone(), box arg))?;
                    }
                    let result = self.run_func(func)?;
                    self.end_ctx();
                    result
                },
                CondF(pairs) => {
                    for (exp, val) in pairs {
                        match self.run_func(exp)? {
                            Atom(name) if name.as_str() == "T" => return self.run_func(val),
                            _                                  => {}
                        }
                    }
                    Nil
                },
                CustomF(nm, args) => match self.lookup_var(&nm)? {
                    LambdaD(pars, func) => self.run_func(LambdaA(box LambdaF(pars, func), args))?,
                    _                   => Err(format!("{} is not a function!", nm))?
                },
                NullF(box fnc) => match self.run_func(fnc)? {
                    Nil => Atom("T".into()),
                    _   => Atom("F".into())
                },
                other => Err(format!("Invalid function Application! {}", other))?
            }
        );
        // println!("Eval: {:?} = {:?}", func, result.clone());
        result
    }

    fn add_var(&mut self, name: String, func: Func) {
        *self = match self.clone() {
            GCtx(mut map) => {
                map.insert(name, func);
                GCtx(map)
            },
            LCtx(mut map, gtx) => {
                map.insert(name, func);
                LCtx(map, box (*gtx).clone())
            }
        }
    }

    fn strt_ctx(&mut self) {
        *self = LCtx(HashMap::new(), box (*self).clone())
    }

    fn end_ctx(&mut self) {
        *self = match (*self).clone() {
            LCtx(_, box ctx) => ctx,
            GCtx(_)          => Env::new()
        }
    }

    fn compile(&mut self, source_code: String, debug: bool) -> Result<(), String> {
        let tokens = tokenize(source_code)?;
        if debug {
            println!("Tokens: {:?}", tokens);
        }
        let exps   = parse(tokens)?;
        if debug {
            println!("S-Expression: {:?}", exps);
        }
        let funcs: Vec<Func>  = exps.iter().map(|exp| self.parse_func((*exp).clone()).unwrap()).collect();
        if debug {
            println!("Func: {:?}", funcs);
        }
        let results: Vec<SExp> = funcs.iter().map(|func| self.run_func((*func).clone()).unwrap()).collect();
        if debug {
            println!("Evaluated S-Expression: {:?}", results);
        }
        for result in results {
            println!("{}", result);
        }
        Ok(())
    }
}

fn tokenize(source_code: String) -> Result<Vec<String>, String> {
    let mut tokens = Vec::new();
    let mut token  = String::new();
    for ch in source_code.chars() {
        match ch {
            c@('(' | ')') => {
                if !token.is_empty() {
                    tokens.push(token);
                    token = String::new();
                }
                tokens.push(c.to_string());
            },
            c@('A'..='Z') => {
                token.push(c);
            },
            c@('0'..='9') => {
                if token.is_empty() {
                    Err("Syntax Error: Atom cannot start with a digit!")?;
                }
                token.push(c);
            },
            c if c.is_whitespace() => {
                if !token.is_empty() {
                    tokens.push(token);
                    token = String::new();
                }
            },
            c => Err(format!("Invalid Character! {}", c))?
        }
    }
    Ok(tokens)
}

#[derive(Debug)]
enum ParserResult {
    OPrn,
    Exp(SExp)
}

fn parse(tokens: Vec<String>) -> Result<Vec<SExp>, String> {
    let mut stack: Vec<ParserResult> = Vec::new();

    for token in tokens {
        match token.as_str() {
            "(" => stack.push(OPrn),
            ")" => {
                let mut exp = Nil;
                loop {
                    let last = stack.pop().ok_or("Empty stack!")?;
                    match last {
                        OPrn             => break,
                        Exp(exp0)       => exp = Cons(box exp0, box exp)
                    }
                }
                stack.push(Exp(exp));
            },
            tkn => stack.push(Exp(Atom(tkn.into())))
        }
    }

    Ok(stack.iter()
        .map(|p_exp| match p_exp { Exp(exp) => (*exp).clone(), _ => panic!("Invalid Expression!")})
        .collect())
}

fn repl() {
    let mut env = Env::new();
    let mut debug = false;
    loop {
        print!(">> ");
        let mut line = String::new();
        stdout().flush().unwrap();
        stdin().read_line(&mut line).unwrap();
        line = line.trim().to_string();
        if line.as_str() == "exit" { break }
        if line.as_str() == "debug" { debug = !debug; }
        match env.compile(line, debug) {
            Err(msg) => println!("{}", msg),
            _        => {}
        }
    }
}

fn main() {
    repl();
}
