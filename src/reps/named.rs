pub use self::Named::*;

#[derive(PartialEq, Clone, Eq, Debug)]
// Bound vars start @ 1
pub enum Named {
    Var(isize),
    Lam(Box<Named>),
    App(Box<Named>, Box<Named>)
}

// Returns a Var with the given name
pub fn var(n: isize) -> Named {
    Var(n)
}

pub fn lam(e: Named) -> Named {
    Lam(Box::new(e))
}

pub fn app(lhs: Named, rhs: Named) -> Named {
    App(Box::new(lhs), Box::new(rhs))
}

impl Named {
    pub fn shift_fv(&mut self, shift: isize, depth: isize) {
        match self {
            Var(ref mut i) => {
               if *i > depth {
                *i += shift
               } 
            }
            Lam(ref mut t) => {
                t.shift_fv(shift, depth + 1)
            }
            App(ref mut lhs, ref mut rhs) => {
                lhs.shift_fv(shift, depth);
                rhs.shift_fv(shift, depth);
            }
        }
    }

    // Substitue var at depth with rhs, and decrement free vars
    pub fn subst_decr(&mut self, rhs: &Named, depth: isize) {
        match self {
            Var(i) => {
                if *i == depth {
                    *self = rhs.to_owned();
                    self.shift_fv(depth - 1, 0)
                }
                else if *i > depth {
                    *i -= 1
                }
            }
            Lam(ref mut t) => {
                t.subst_decr(rhs, depth + 1)
            }
            App(ref mut app_lhs, ref mut app_rhs) => {
                app_lhs.subst_decr(rhs, depth);
                app_rhs.subst_decr(rhs, depth);
            }
        }
    }

    pub fn apply(&mut self, rhs: &Named) -> Result<(), ()> {
        match self {
            Lam(t) => {
                *self = *t.to_owned()
            }
            _ => return Err(())
        }
        self.subst_decr(rhs, 1);
        return Ok(())
    }

    // pub fn reduce(&mut self) -> bool {
    //     match self {
    //         App 
            
    //     }
    //     false
    // }
}