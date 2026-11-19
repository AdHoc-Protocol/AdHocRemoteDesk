// The program of a computer: the host of src/lib.rs, started from a console or by a double click.

fn main() {
    adhoc_remotedesk::os::init();
    adhoc_remotedesk::os::main(adhoc_remotedesk::session::run);
}
