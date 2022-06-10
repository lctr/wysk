#[cfg(test)]
mod test {
    use std::path::{Path, PathBuf};

    #[test]
    fn compiler_loc() {
        fn is_rs_file(path: &impl AsRef<Path>) -> bool {
            path.as_ref()
                .extension()
                .and_then(|s| s.to_str())
                .map(|s| s.ends_with("rs"))
                .unwrap_or_else(|| false)
        }
        let mut paths = vec![];
        let mut loc = 0;
        let mut queue: Vec<PathBuf> = vec![PathBuf::from("../../")];
        while let Some(x) = queue.pop() {
            if x.is_file() {
                if is_rs_file(&x) {
                    paths.push(x);
                }
            } else if x.is_dir() {
                for dir in std::fs::read_dir(x) {
                    for entry in dir {
                        if let Ok(p) = entry.map(|e| e.path()) {
                            if p.is_dir() {
                                queue.push(p);
                            } else if is_rs_file(&p) {
                                if let Ok(st) = std::fs::read_to_string(&p) {
                                    st.lines().for_each(|_| loc += 1);
                                }
                                paths.push(p);
                            }
                        }
                    }
                }
            }
        }

        println!("loc: {}", loc);
        println!("files: {:#?}", paths)
    }
}
