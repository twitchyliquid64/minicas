/// A compact representation of the path to take through an AST to
/// reach a certain node.
#[derive(Debug, Clone, Eq, Hash)]
pub enum Path {
    Opt(u64, usize),
    Vec(Vec<usize>),
}

impl Default for Path {
    fn default() -> Self {
        Self::Opt(0, 0)
    }
}

impl PartialEq for Path {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl From<Vec<usize>> for Path {
    fn from(v: Vec<usize>) -> Path {
        let mut out = Path::default();
        for v in v.into_iter() {
            out.push(v);
        }
        out
    }
}

impl Into<Vec<usize>> for Path {
    fn into(self: Self) -> Vec<usize> {
        self.iter().collect()
    }
}

impl Path {
    pub fn with_next(u: usize) -> Self {
        let mut out = Self::default();
        out.push(u);
        out
    }

    pub fn push(&mut self, u: usize) {
        match self {
            Self::Opt(v, cnt) => match stuffed_val_push(*v, u) {
                Ok(new_v) => {
                    *v = new_v;
                    *cnt += 1;
                }
                Err(()) => {
                    let mut new_v: Vec<usize> = self.iter().collect();
                    new_v.push(u);
                    *self = Self::Vec(new_v);
                }
            },
            Self::Vec(v) => v.push(u),
        }
    }

    pub fn iter<'a>(&'a self) -> PathIter<'a> {
        PathIter {
            path: self,
            offset: 0,
        }
    }
}

/// An iterator over the values in a [Path].
pub struct PathIter<'a> {
    path: &'a Path,
    offset: usize,
}

impl Iterator for PathIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        match self.path {
            Path::Opt(v, cnt) => {
                if self.offset >= *cnt {
                    None
                } else {
                    self.offset += 1;
                    let possible = v >> ((cnt - self.offset) * 4);
                    if possible == 0 {
                        None
                    } else if (possible & 0b11) == 0b11 {
                        todo!("support longer formats")
                    } else {
                        Some(((possible >> 1) & 0b1) as usize)
                    }
                }
            }
            Path::Vec(v) => {
                if self.offset >= v.len() {
                    None
                } else {
                    self.offset += 1;
                    Some(v[self.offset - 1])
                }
            }
        }
    }
}

#[inline(always)]
fn stuffed_val_full(v: &u64) -> bool {
    (v >> 60) != 0
}

#[inline(always)]
fn stuffed_val_push(v: u64, n: usize) -> Result<u64, ()> {
    if stuffed_val_full(&v) {
        return Err(());
    }
    if n > 1 {
        return Err(());
    }

    Ok((v << 4) | (n << 1) as u64 | if n == 0 { 1 } else { 0 })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opt() {
        let mut path = Path::default();
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![]);

        path.push(0);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0]);
        path.push(1);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1]);
        path.push(0);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1, 0]);
        assert!(!matches!(path, Path::Vec(_)));
    }

    #[test]
    fn vec() {
        let mut path = Path::default();
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![]);

        path.push(2);
        assert!(matches!(path, Path::Vec(_)));
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![2]);
        path.push(1);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![2, 1]);
        path.push(0);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![2, 1, 0]);
    }

    #[test]
    fn vec_promote() {
        let mut path = Path::default();
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![]);

        path.push(0);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0]);
        path.push(1);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1]);
        path.push(0);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1, 0]);
        assert!(!matches!(path, Path::Vec(_)));
        path.push(88);
        assert!(matches!(path, Path::Vec(_)));
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1, 0, 88]);
        path.push(1);
        assert_eq!(path.iter().collect::<Vec<_>>(), vec![0, 1, 0, 88, 1]);
    }
}
