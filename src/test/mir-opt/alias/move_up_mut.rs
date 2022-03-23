///// #[inline(never)]
// EMIT_MIR move_up_mut.move_up_mut.Alias.diff
fn move_up_mut(x: &mut i32, y: &mut i32) -> i32 {
    *x = 42;
    *y = 7;
    return *x;
}

fn main() {
    let mut x = 1;
    let mut y = 2;
    move_up_mut(&mut x, &mut y);
}
