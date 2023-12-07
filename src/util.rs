pub(crate) fn remove_value<T: Eq>(vals: &mut Vec<T>, val: &T) -> bool {
    let mut to_remove = None;
    for (idx, v) in vals.iter().enumerate() {
        if v == val {
            to_remove = Some(idx);
            break;
        }
    }
    let Some(idx) = to_remove else {
        return false;
    };
    vals.remove(idx);
    true
}
