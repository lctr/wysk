#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleId(u32);

impl ModuleId {
    pub fn new(n: u32) -> Self {
        Self(n)
    }

    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl std::ops::Add<u32> for ModuleId {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl std::ops::AddAssign<u32> for ModuleId {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs
    }
}

impl std::fmt::Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ModuleId({})", &self.0)
    }
}
