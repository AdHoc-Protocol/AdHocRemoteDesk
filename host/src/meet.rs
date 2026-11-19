// The meeting through a relay of AdHoc Relay: the machine behind its NAT, the viewer behind another.
//
// The line of the password ends in 👉: an answer comes. The machine asks the relay for a port of meeting - the password, 16
// characters, and its own 8 random bytes, its id, to the port of requests; the relay answers with a port nobody holds, given
// to that id - and shows the line to give the viewer: the relay, that port and the token. At once it knocks at that port
// with the password and the id ( one UDP packet ) - again every 20 s, and at once after a meeting, at a new address of the relay
// or when the port refuses - and dials it, a try of up to 10 s after another, from one source port; the relay drops those SYNs,
// and only an address that knocked waits there. The viewer dials the same port; the relay sends its SYN on to the machine, as if
// from itself: the two meet, and the server takes the connection as if it had accepted it. The machine goes on waiting at the
// same port, from a new source port: a viewer that lost its connection, another viewer, or the machine started again as
// administrator meets there again. The port is given to the id, not to an address: a NAT that gives the machine another address,
// or another port for each try, keeps it.
//
// A fixed port - the line has no 👉 at its end - is the relay's for one key: nothing is asked, the key alone knocks at it,
// and the viewer's line is the same at every start. A relay whose address changes is read where its record is kept: the
// line names, after the key, 🌐 and each read key, 👉 and the relay of fixed address that keeps it, then 🌐 and the port of
// the relay; the machine reads the address there, the freshest, and again every 30 s while it waits - moved, it asks again
// there with the same id, or knocks there, from the same source port: the relay knows the side that waits by it. The signs
// may be typed as > and @.

use std::io;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, TcpStream, ToSocketAddrs, UdpSocket};
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

use socket2::{Domain, Protocol, Socket, Type};

use crate::lib::network::TCP::Server;

/// How long one try of dialing waits: the relay drops its SYN until the viewer comes, the system sends it again within the try -
/// the relay keeps the side that waits 15 s after its last SYN.
const TRY: Duration = Duration::from_secs(10);

/// A try refused, or the network down: the next one no sooner than this after the last began - a pause, not a storm of tries.
const PAUSE: Duration = Duration::from_secs(2);

/// How often the knock goes - the relay keeps the port open `wait` seconds after it, 60 by default: two may be lost -, and at
/// once at the start, after a meeting, at a new address of the relay, and when a try is refused. Each knock carries the password or
/// the key: the fewer, the less a watcher sees.
const KNOCK: Duration = Duration::from_secs(20);

/// How long one request waits for its answer.
const ANSWER: Duration = Duration::from_secs(1);

/// How often the address of a relay is looked at again while the machine waits: a name looked up, a record read.
const LOOK: Duration = Duration::from_secs(30);

/// A record written within this many minutes is taken at once; an older one only when no relay has a fresher.
const FRESH: u8 = 2;

/// The port of requests of a relay when none is given: the first port of the range AdHoc Relay installs.
pub const ASKS: u16 = 40000;

/// The length of the password of a relay, of the key of a fixed port, of a read key.
pub const KEY: usize = 16;

/// Where the relay is.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Where {
    /// Itself: a name or an address, and its port of requests - or, for a fixed port, that port.
    Point(String, u16),
    /// Read where its record is kept, in this order: the read key, the relay of fixed address - a name or an address -, its
    /// port of requests; and the port of the relay itself, of requests or the fixed one: the record has its address alone.
    Read(Vec<([u8; KEY], String, u16)>, u16),
}

/// What the machine meets its viewer with.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Meet {
    /// The password of the relay, or the key of its fixed port.
    pub key:   [u8; KEY],
    /// A fixed port: knocked at with the key alone, nothing asked.
    pub fixed: bool,
    pub at:    Where,
}

impl Meet {
    /// A line as its owner gives it - the page of AdHoc Relay copies it so: `Tr7kQ2xZp4Lm9sWd👉router.example.org:40000👉`,
    /// `Fx2pL8wNq7Rk3mZa👉router.example.org:41000`, `Fx2pL8wNq7Rk3mZa🌐Rk8mP2qLx3Vb7NtY👉203.0.113.7:40000🌐...🌐41000` - apart, in
    /// the signs of the keyboard: the password or the key, when it is there, and the rest, from the first `>` or `@` on. A password
    /// has no 👉 or 🌐, nor a name or an address.
    pub fn given(text: &str) -> (Option<String>, String) {
        let text = plain(text);
        match text.find(['>', '@']) {
            Some(i) if i > 0 => (Some(text[..i].to_string()), text[i..].to_string()),
            _ => (None, text),
        }
    }

    /// The rest of a line, as `given` makes it: a fixed port or not, and where the relay is; Err - what is wrong with it. `>`
    /// first and last: a port asked for, an answer comes; `>` first alone: a fixed port; `@` first: the address read, `@` before
    /// each `read key>keeper:port` and before the port of the relay, `>` last when a port is asked for; no sign: the relay
    /// alone, a port asked for.
    pub fn place(rest: &str) -> Result<(bool, Where), String> {
        let rest = plain(rest);
        let (fixed, read, rest) = if rest.contains(['>', '@']) {
            let asks = rest.ends_with('>');
            let r = rest.strip_suffix('>').unwrap_or(&rest);
            let (read, r) = match (r.strip_prefix('>'), r.strip_prefix('@')) {
                (Some(r), _) => (false, r),
                (_, Some(r)) => (true, r),
                _ => return Err(format!("{}: the password or the key, 👉 and the relay, or 🌐 and where its address is read", pretty(&rest))),
            };
            (!asks, read, r)
        } else {
            (false, false, rest.as_str())
        };
        // a port: 1…65535, in digits alone
        let port = |text: &str| -> Option<u16> { (text.len() <= 5 && text.bytes().all(|b| b.is_ascii_digit())).then(|| text.parse().ok()).flatten().filter(|&p| p != 0) };
        // a name or an address, and the port after : - `none` when there is none
        let point = |text: &str, none: Option<u16>| -> Option<(String, u16)> {
            let (point, port) = match text.rsplit_once(':') {
                Some((point, p)) => (point, port(p)?),
                None => (text, none?),
            };
            (!point.is_empty() && !point.contains(|c: char| c.is_whitespace() || ":@=,!?>".contains(c))).then(|| (point.to_string(), port))
        };
        // 🌐 between the parts: each where the address is read - a read key 👉 a relay and its port -, and after the last 🌐 the port
        // of the relay
        if read {
            let mut parts: Vec<&str> = rest.split('@').collect();
            let at = parts.pop().and_then(port).filter(|_| !parts.is_empty());
            let at = at.ok_or_else(|| format!("🌐{}: after the relays that keep its address, 🌐 and the port of the relay", pretty(rest)))?;
            let mut reads = Vec::new();
            for r in parts {
                let r = r.trim();
                let (key, keeper) = r.split_once('>').ok_or_else(|| format!("{}: a read key, 👉, a relay, :, its port - 🌐 between them", pretty(r)))?;
                let key = Self::key(key).ok_or_else(|| format!("{key}: a read key is {KEY} letters and digits"))?;
                let (keeper, asks) = point(keeper, None).ok_or_else(|| format!("{keeper}: a name or an address, and after : its port of requests"))?;
                reads.push((key, keeper, asks));
            }
            return Ok((fixed, Where::Read(reads, at)));
        }
        match point(rest, if fixed { None } else { Some(ASKS) }) {
            Some((point, port)) => Ok((fixed, Where::Point(point, port))),
            None if fixed => Err(format!("{rest}: a name or an address, and after : the fixed port, such as router.example.org:41000")),
            None => Err(format!("{rest}: a name or an address, and after : the port of requests, such as router.example.org:40000")),
        }
    }

    /// The meeting of `key` - the password or the key of a fixed port - and the rest of its line, as `given` makes it.
    pub fn of(key: &str, rest: &str) -> Result<Meet, String> {
        let (fixed, at) = Self::place(rest)?;
        let key = Self::key(key).ok_or_else(|| {
            if fixed { format!("the key of a fixed port is {KEY} letters and digits") } else { format!("the password of a relay is {KEY} letters and digits") }
        })?;
        Ok(Meet { key, fixed, at })
    }

    /// 16 letters and digits; None - other than that, a space too.
    fn key(text: &str) -> Option<[u8; KEY]> { <[u8; KEY]>::try_from(text.as_bytes()).ok().filter(|k| k.iter().all(u8::is_ascii_alphanumeric)) }
}

/// A line in the signs of the keyboard: 👉 >, 🌐 @, 👀 ?, ✏️ ! - what makes an emoji coloured, and the colour of skin, left out; the
/// spaces around it too.
pub fn plain(text: &str) -> String {
    let text: String = text.chars().filter(|c| !matches!(c, '\u{FE0F}' | '\u{1F3FB}'..='\u{1F3FF}')).map(|c| match c { '👉' => '>', '🌐' => '@', '👀' => '?', '\u{270F}' => '!', c => c }).collect();
    text.trim().to_string()
}

/// A line as people see it - and as it is kept: the signs of the keyboard as emoji.
pub fn pretty(text: &str) -> String {
    text.chars().map(|c| match c { '>' => "👉".to_string(), '@' => "🌐".to_string(), '?' => "👀".to_string(), '!' => "\u{270F}\u{FE0F}".to_string(), c => c.to_string() }).collect()
}

/// The port of meeting and the id it is given to: the machine started again as administrator knocks there at once, as `--meet-given`.
/// None for a fixed port: its key opens it, at every start. Another port, when the relay moved and gave another.
static GIVEN: Mutex<Option<(u16, [u8; 8])>> = Mutex::new(None);

/// `--meet-given` of the machine started again: the port, `.`, the id in 16 hex digits.
pub fn given() -> Option<String> {
    GIVEN.lock().unwrap().map(|(port, id)| format!("{port}.{}", id.iter().map(|b| format!("{b:02x}")).collect::<String>()))
}

/// `--meet-given` back: the port and the id.
pub fn parse_given(text: &str) -> Option<(u16, [u8; 8])> {
    let (port, id) = text.split_once('.')?;
    let id = u64::from_str_radix(id, 16).ok().filter(|_| id.len() == 16)?;
    Some((port.parse().ok().filter(|&p| p != 0)?, id.to_be_bytes()))
}

/// Shows the line for the viewer and meets the viewers from then on: at the port given before this start, when there is one.
pub fn start(meet: Meet, server: Server, given: Option<(u16, [u8; 8])>, pass: String) {
    thread::Builder::new()
        .name("meet".into())
        .spawn(move || {
            run(meet, given, |point, port| {
                // one line for the viewer: the address of the meeting and, after /, the token and the check of the key - the page takes it whole
                crate::console::line_to_send(&format!("{point}:{port}/{pass}"));
            }, |stream, at| {
                if let Err(e) = server.adopt(stream) {
                    say!("❌", Bad, "The meeting at {at}: {e}");
                }
            })
        })
        .expect("a thread of the meeting");
}

/// The port of Remote Desktop of Windows: what the line of a relay to it is for.
pub const MSTSC: u16 = 3389;

/// The relay: AdHoc Relay as the way to another server of this computer, or of its network - `to`, such as `127.0.0.1:3389`, Remote
/// Desktop of Windows. Whoever dials the port of meeting, with its own program - Remote Desktop Connection, ssh, a VNC viewer -, is
/// joined to `to`: the bytes go as they are, both ways, the server there checks who comes. Runs as long as the program.
pub fn relay(meet: Meet, to: String) {
    let rdp = to.rsplit_once(':').is_some_and(|(_, p)| p == MSTSC.to_string());
    // nothing there to reach: said at once, the meetings wait for it anyway
    match to.to_socket_addrs().map(|mut a| a.next()) {
        Ok(Some(at)) if TcpStream::connect_timeout(&at, Duration::from_secs(2)).is_ok() => say!("🔌", Good, "{to} answers: whoever comes is joined to it"),
        _ if rdp => say!("⚠️", Warn, "Nothing answers at {to}: Remote Desktop is off on this computer. Windows Pro or above: Settings > System > Remote Desktop, on. Windows Home has none"),
        _ => say!("⚠️", Warn, "Nothing answers at {to} yet: whoever comes waits for it"),
    }
    if rdp {
        say!("🔑", Warn, "Whoever finds the port will try passwords: programs of the internet guess at every Remote Desktop they find, day and night");
        say!("🔑", Warn, "The account you log in with needs a long password of its own, 16 characters or more, used nowhere else; not Administrator, admin or user");
    }
    run(meet, None, |point, port| {
        let line = format!("{point}:{port}");
        if rdp {
            say!("🖥️", News, "Remote Desktop Connection ( mstsc ) of another computer reaches this one at it: as the computer, type");
        } else {
            say!("🔗", News, "A program of another computer reaches {to} at it: as the address and the port, type");
        }
        crate::console::line_to_send(&line);
    }, |stream, at| {
        let to = to.clone();
        let _ = thread::Builder::new().name("relay".into()).spawn(move || join(stream, &to, at));
    });
}

/// `came` - a connection that met through the relay - joined to `to` till either side ends.
fn join(came: TcpStream, to: &str, at: SocketAddrV4) {
    let there = match to.to_socket_addrs().ok().and_then(|mut a| a.next()).ok_or_else(|| io::Error::other("no such address")).and_then(|a| TcpStream::connect_timeout(&a, Duration::from_secs(5))) {
        Ok(there) => there,
        Err(e) => return say!("❌", Bad, "Someone came through {at}; {to}: {e}"),
    };
    say!("✅", Good, "Someone came through {at}: joined to {to}");
    let _ = came.set_nodelay(true);
    let _ = there.set_nodelay(true);
    let (Ok(mut came_in), Ok(mut there_out)) = (came.try_clone(), there.try_clone()) else { return };
    let (mut came_out, mut there_in) = (came, there);
    // each way on a thread of its own: its end is told the other side, which ends in its turn
    let back = thread::spawn(move || {
        let n = io::copy(&mut there_in, &mut came_out).unwrap_or(0);
        let _ = came_out.shutdown(std::net::Shutdown::Write);
        n
    });
    let sent = io::copy(&mut came_in, &mut there_out).unwrap_or(0);
    let _ = there_out.shutdown(std::net::Shutdown::Write);
    let got = back.join().unwrap_or(0);
    say!("👋", Quiet, "Gone, the one through {at}: {} in, {} out", bytes(sent), bytes(got));
}

fn bytes(n: u64) -> String {
    match n {
        n if n >= 1 << 30 => format!("{:.1} GB", n as f64 / (1u64 << 30) as f64),
        n if n >= 1 << 20 => format!("{:.1} MB", n as f64 / (1u64 << 20) as f64),
        n if n >= 1 << 10 => format!("{:.1} KB", n as f64 / 1024.0),
        n => format!("{n} B"),
    }
}

/// Where the relay is now: its address, its port - of requests, or the fixed one -, and how the viewer's line names it.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Place {
    ip:   Ipv4Addr,
    port: u16,
    name: String,
}

/// The meeting, for whatever then takes the connections: the port asked for - or the one `given` before this start, or the fixed
/// one -, `show` told the relay and the port, again when they change, and from then on each connection that meets goes to
/// `took`, the next awaited at once.
fn run(meet: Meet, given: Option<(u16, [u8; 8])>, mut show: impl FnMut(&str, u16), mut took: impl FnMut(TcpStream, SocketAddrV4)) {
    // one socket for the request, the reads and the knocks, from one source port: the NAT of the machine keeps one mapping for them
    let udp = match UdpSocket::bind((Ipv4Addr::UNSPECIFIED, 0)) {
        Ok(udp) => udp,
        Err(e) => return say!("❌", Bad, "The meeting: {e}"),
    };
    let id = given.map(|(_, id)| id).unwrap_or_else(|| {
        let mut id = [0u8; 8];
        getrandom::fill(&mut id).expect("the random numbers of the system");
        id
    });
    // the knock: the password and the id - the request for the port too -, or the key of a fixed port alone
    let knock: Vec<u8> = if meet.fixed { meet.key.to_vec() } else { [&meet.key[..], &id[..]].concat() };
    let mut place = loop {
        match locate(&udp, &meet) {
            Ok(place) => break place,
            Err(e) => {
                say!("❌", Bad, "{e}: again in 5 s");
                thread::sleep(Duration::from_secs(5));
            }
        }
    };
    let mut port = match (meet.fixed, given) {
        (true, _) => place.port, // its key opens it
        (false, Some((port, _))) => port, // given before this start, to this id: its knocks open it
        (false, None) => match ask(&udp, &place, &knock) {
            Ok(port) => port,
            Err(e) => return say!("❌", Bad, "The relay {}: {e}", place.name),
        },
    };
    if !meet.fixed {
        *GIVEN.lock().unwrap() = Some((port, id));
    }
    show(&place.name, port);
    say!("👀", Wait, "Waiting for whoever connects…");
    crate::console::stay_awake();
    // the source port of the dialing: kept till someone comes - a relay that moves too knows the machine by it
    let mut from = SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0));
    // the port of meeting is not sure at the address of now: asked again at the next look
    let mut unsure = false;
    let mut look = Instant::now() + LOOK;
    // when the knock went last: None - it goes at once
    let mut knocked: Option<Instant> = None;
    loop {
        let at = SocketAddrV4::new(place.ip, port);
        match once(&udp, at, &knock, &mut from, &mut knocked, look) {
            Ok(Some(stream)) => {
                took(stream, at);
                from = SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0));
                continue;
            }
            Ok(None) => {}
            Err(e) => {
                say!("❌", Bad, "The meeting at {at}: {e}");
                thread::sleep(PAUSE);
                if Instant::now() < look {
                    continue;
                }
            }
        }
        // every 30 s: where the relay is now - a name looked up again, a record read again
        look = Instant::now() + LOOK;
        let now = match locate(&udp, &meet) {
            Ok(now) => now,
            Err(e) => {
                say!("⚠️", Warn, "{e}: knocking on at {at}");
                continue;
            }
        };
        let moved = now.ip != place.ip || now.port != place.port;
        if !moved && !unsure {
            continue;
        }
        let was = (place.name.clone(), port);
        place = now;
        if meet.fixed {
            port = place.port;
        } else {
            match ask(&udp, &place, &knock) {
                Ok(got) => {
                    port = got;
                    unsure = false;
                    *GIVEN.lock().unwrap() = Some((port, id));
                }
                Err(e) => {
                    unsure = true;
                    say!("⚠️", Warn, "The relay {}: {e} - knocking at {port} there, asking again in 30 s", place.name);
                }
            }
        }
        // at a new address, or another port: knocked at once
        knocked = None;
        if (place.name.clone(), port) != was {
            say!("🔀", News, "The relay moved: the line is new");
            show(&place.name, port);
            say!("👀", Wait, "Waiting for whoever connects…");
        } else if moved {
            say!("🔀", Quiet, "The relay moved to {}: the line stays", place.ip);
        }
    }
}

/// Knocks at `at` and dials it until the viewer comes or `until` - from one source port, `from`, kept for the next call, so the NAT
/// of the machine keeps one mapping. The knock goes when `knocked` - when it went last, kept for the next call - is `KNOCK` ago or
/// None: None again once a try met - the meeting closed the port - or was refused. None - nobody came by `until`.
fn once(udp: &UdpSocket, at: SocketAddrV4, knock: &[u8], from: &mut SocketAddr, knocked: &mut Option<Instant>, until: Instant) -> io::Result<Option<TcpStream>> {
    let to = SocketAddr::V4(at).into();
    while Instant::now() < until {
        if knocked.is_none_or(|k| k.elapsed() >= KNOCK) {
            let _ = udp.send_to(knock, at); // a lost knock shows as a refused try below
            *knocked = Some(Instant::now());
        }
        let tcp = Socket::new(Domain::IPV4, Type::STREAM, Some(Protocol::TCP))?;
        tcp.set_reuse_address(true)?;
        tcp.bind(&(*from).into())?;
        if from.port() == 0 {
            *from = tcp.local_addr()?.as_socket().ok_or_else(|| io::Error::other("no local address"))?;
        }
        let started = Instant::now();
        match tcp.connect_timeout(&to, until.saturating_duration_since(started).clamp(Duration::from_secs(1), TRY)) {
            Ok(()) => {
                *knocked = None; // the meeting closed the port: the next try knocks at once
                return Ok(Some(tcp.into()));
            }
            Err(e) => {
                // refused: the port is not open - the knock was lost, or came late -: knocked again at once
                if e.kind() != io::ErrorKind::TimedOut {
                    *knocked = None;
                }
                // refused at once, or the network is down: a pause, not a storm of tries
                if let Some(rest) = PAUSE.checked_sub(started.elapsed()) {
                    thread::sleep(rest)
                }
            }
        }
    }
    Ok(None)
}

fn ipv4(host: &str) -> io::Result<Ipv4Addr> {
    (host, 0)
        .to_socket_addrs()?
        .find_map(|a| match a {
            SocketAddr::V4(a) => Some(*a.ip()),
            SocketAddr::V6(_) => None,
        })
        .ok_or_else(|| io::Error::other("no IPv4 address"))
}

/// The answer of `length` bytes from `to` to `request`, sent up to `tries` times, `ANSWER` each. None - no answer.
fn answer(udp: &UdpSocket, to: SocketAddr, request: &[u8], length: usize, tries: u32) -> io::Result<Option<[u8; 8]>> {
    let mut got = [0u8; 8];
    for _ in 0..tries {
        udp.send_to(request, to)?;
        let started = Instant::now();
        while let Some(left) = ANSWER.checked_sub(started.elapsed()).filter(|left| !left.is_zero()) {
            udp.set_read_timeout(Some(left))?;
            match udp.recv_from(&mut got) {
                Ok((n, from)) if n == length && from == to => return Ok(Some(got)),
                Ok(_) => {} // not the answer
                // no answer in time, or refused at once: the request again after the rest of the second
                Err(_) => thread::sleep(ANSWER.saturating_sub(started.elapsed())),
            }
        }
    }
    Ok(None)
}

/// Where the relay is now. Itself: its name looked up. Read: each relay that keeps its record in turn, 3 tries of
/// a second each - the answer the address and the minutes since it wrote it, 5 bytes, the port of the line; one written within 2
/// minutes is taken at once, else the freshest of all.
fn locate(udp: &UdpSocket, meet: &Meet) -> Result<Place, String> {
    let (reads, port) = match &meet.at {
        Where::Point(point, port) => {
            let ip = ipv4(point).map_err(|e| format!("The relay {point}: {e}"))?;
            return Ok(Place { ip, port: *port, name: point.clone() });
        }
        Where::Read(reads, port) => (reads, *port),
    };
    let mut best: Option<(u8, Place)> = None;
    for (key, point, asks) in reads {
        let Ok(ip) = ipv4(point) else { continue };
        let Ok(Some(got)) = answer(udp, SocketAddr::V4(SocketAddrV4::new(ip, *asks)), key, 5, 3) else { continue };
        let ip = Ipv4Addr::new(got[0], got[1], got[2], got[3]);
        let place = Place { ip, port, name: ip.to_string() };
        let age = got[4];
        if best.as_ref().is_none_or(|(a, _)| age < *a) {
            best = Some((age, place));
        }
        if age <= FRESH {
            break;
        }
    }
    best.map(|(_, place)| place).ok_or_else(|| {
        let names = reads.iter().map(|(_, point, asks)| format!("{point}:{asks}")).collect::<Vec<_>>().join(", ");
        format!("No address of the relay from {names}: a wrong read key, the relay has not written its address there yet, or this address is blocked for wrong keys")
    })
}

/// A port of meeting from the relay: the password and the id to its port of requests, the answer a port of 2 bytes, high
/// first, given to that id. A request or an answer lost is asked again: the relay gives the same port to the same id - also
/// at another address of it, when it moved.
fn ask(udp: &UdpSocket, place: &Place, request: &[u8]) -> io::Result<u16> {
    let at = SocketAddr::V4(SocketAddrV4::new(place.ip, place.port));
    match answer(udp, at, request, 2, 10)? {
        Some(got) => Ok(u16::from_be_bytes([got[0], got[1]])),
        None => Err(io::Error::other(format!("no port of meeting from {at}: a wrong password, a wrong first port or this address is blocked for wrong knocks"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::net::TcpListener;

    /// A connection that met, joined to a server: what goes in comes back, both ways, and the end of one side ends the other.
    #[test]
    fn relay_joins_both_ways() {
        // the server of this computer: an echo, upper case
        let server = TcpListener::bind("127.0.0.1:0").unwrap();
        let to = server.local_addr().unwrap().to_string();
        thread::spawn(move || {
            let (mut s, _) = server.accept().unwrap();
            let mut all = Vec::new();
            s.read_to_end(&mut all).unwrap();
            s.write_all(&all.to_ascii_uppercase()).unwrap();
        });
        // the connection of the meeting: its far end is the one who came
        let meeting = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut came = TcpStream::connect(meeting.local_addr().unwrap()).unwrap();
        let (met, _) = meeting.accept().unwrap();
        let at = SocketAddrV4::new(Ipv4Addr::LOCALHOST, 41933);
        let joined = thread::spawn(move || join(met, &to, at));
        let sent = vec![b'x'; 300_000];
        came.write_all(&sent).unwrap();
        came.shutdown(std::net::Shutdown::Write).unwrap();
        let mut back = Vec::new();
        came.read_to_end(&mut back).unwrap();
        assert_eq!(back, vec![b'X'; 300_000]);
        joined.join().unwrap();
    }

    #[test]
    fn given_goes_back() {
        let id = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        *GIVEN.lock().unwrap() = Some((41933, id));
        let text = given().unwrap();
        assert_eq!(text, "41933.0123456789abcdef");
        assert_eq!(parse_given(&text), Some((41933, id)));
        assert_eq!(parse_given("41933"), None);
        assert_eq!(parse_given("41933.0123"), None);
        assert_eq!(parse_given("0.0123456789abcdef"), None);
    }

    /// Every line of `lines.tsv` - a copy of `docs/lines.tsv` of AdHoc Relay: this makes of it what the file says, as the scripts of the
    /// server of AdHoc Relay and a DeFreez host do. The line whole, in the signs of the keyboard, the ports put in where the line has
    /// none, or `error`.
    #[test]
    fn the_lines_of_adhoc_relay() {
        let text = |m: &Meet| {
            let at = match &m.at {
                Where::Point(point, port) => format!(">{point}:{port}"),
                Where::Read(reads, port) => format!("{}@{port}", reads.iter().map(|(k, point, asks)| format!("@{}>{point}:{asks}", String::from_utf8_lossy(k))).collect::<String>()),
            };
            format!("{}{at}{}", String::from_utf8_lossy(&m.key), if m.fixed { "" } else { ">" })
        };
        let mut cases = 0;
        for case in include_str!("lines.tsv").lines().filter(|l| !l.is_empty() && !l.starts_with('#')) {
            let (line, want) = case.split_once('\t').expect("a line, a tab, what it is");
            let got = match Meet::given(line) {
                (Some(key), rest) => Meet::of(&key, &rest).map(|m| text(&m)).unwrap_or_else(|_| "error".into()),
                (None, _) => "error".into(),
            };
            assert_eq!(got, want, "the line '{line}'");
            cases += 1;
        }
        assert!(cases > 30);
    }

    /// Every form of the line: apart, and the meeting of it.
    #[test]
    fn the_lines() {
        let key = |k: &str| <[u8; KEY]>::try_from(k.as_bytes()).unwrap();
        // a port given at each start, the address fixed: 👉 at the end; the port of requests, or none - 40000
        assert_eq!(Meet::given("Tr7kQ2xZp4Lm9sWd👉router.example.org:40000👉"), (Some("Tr7kQ2xZp4Lm9sWd".into()), ">router.example.org:40000>".into()));
        assert_eq!(Meet::given(" router.example.org "), (None, "router.example.org".into()));
        assert_eq!(Meet::of("Tr7kQ2xZp4Lm9sWd", "router.example.org"), Ok(Meet { key: key("Tr7kQ2xZp4Lm9sWd"), fixed: false, at: Where::Point("router.example.org".into(), 40000) }));
        assert_eq!(Meet::of("Tr7kQ2xZp4Lm9sWd", ">router.example.org>"), Meet::of("Tr7kQ2xZp4Lm9sWd", "router.example.org"));
        assert_eq!(Meet::of("Tr7kQ2xZp4Lm9sWd", "203.0.113.7:20000").unwrap().at, Where::Point("203.0.113.7".into(), 20000));
        // a fixed port: no 👉 at the end; its port is a must
        assert_eq!(Meet::given("Fx2pL8wNq7Rk3mZa👉router.example.org:41000"), (Some("Fx2pL8wNq7Rk3mZa".into()), ">router.example.org:41000".into()));
        assert_eq!(Meet::of("Fx2pL8wNq7Rk3mZa", ">router.example.org:41000"), Ok(Meet { key: key("Fx2pL8wNq7Rk3mZa"), fixed: true, at: Where::Point("router.example.org".into(), 41000) }));
        assert!(Meet::of("Fx2pL8wNq7Rk3mZa", ">router.example.org").is_err());
        // the address read: the relays in their order, each with its port; the port of the relay last
        let (with, rest) = Meet::given("Tr7kQ2xZp4Lm9sWd🌐Rk8mP2qLx3Vb7NtY👉198.51.100.9:40000🌐 Hx4nT7wAe2Kq9VsM👉s2.example.org:40001🌐41000👉");
        assert_eq!((with.as_deref(), rest.as_str()), (Some("Tr7kQ2xZp4Lm9sWd"), "@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@ Hx4nT7wAe2Kq9VsM>s2.example.org:40001@41000>"));
        assert_eq!(Meet::of("Tr7kQ2xZp4Lm9sWd", &rest).unwrap(), Meet {
            key: key("Tr7kQ2xZp4Lm9sWd"),
            fixed: false,
            at: Where::Read(vec![(key("Rk8mP2qLx3Vb7NtY"), "198.51.100.9".into(), 40000), (key("Hx4nT7wAe2Kq9VsM"), "s2.example.org".into(), 40001)], 41000),
        });
        // given again - the rest as the menu keeps it - it stays as it is
        assert_eq!(Meet::given(&rest), (None, rest.clone()));
        assert_eq!(Meet::given("👉router.example.org:41000"), (None, ">router.example.org:41000".into()));
        // a fixed port, the address read; typed with the signs of the keyboard
        let (with, rest) = Meet::given("Fx2pL8wNq7Rk3mZa@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@41000");
        assert_eq!(rest, "@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@41000");
        let meet = Meet::of(&with.unwrap(), &rest).unwrap();
        assert!(meet.fixed);
        assert_eq!(meet.at, Where::Read(vec![(key("Rk8mP2qLx3Vb7NtY"), "198.51.100.9".into(), 40000)], 41000));
        // as people see it, and back
        assert_eq!(pretty("@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@41000>"), "🌐Rk8mP2qLx3Vb7NtY👉198.51.100.9:40000🌐41000👉");
        assert_eq!(plain("🌐Rk8mP2qLx3Vb7NtY👉198.51.100.9:40000🌐41000👉"), "@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@41000>");
        assert_eq!(plain(" 👉️👉🏽router.example.org "), ">>router.example.org");
        // the line a relay of fixed address gives a changing one: ✏️ the write key, 👀 the read key - as people see it, and back
        assert_eq!(pretty("!Wk3vB9xQm5Tz2Lpe?Rk8mP2qLx3Vb7NtY>198.51.100.9:40000"), "✏️Wk3vB9xQm5Tz2Lpe👀Rk8mP2qLx3Vb7NtY👉198.51.100.9:40000");
        assert_eq!(plain("✏️Wk3vB9xQm5Tz2Lpe👀Rk8mP2qLx3Vb7NtY👉198.51.100.9:40000"), "!Wk3vB9xQm5Tz2Lpe?Rk8mP2qLx3Vb7NtY>198.51.100.9:40000");
        // wrong: a password of 8, a read key of 8, a port of letters, a password with a sign, the old lines, a read with no port of the relay
        assert!(Meet::of("Tr7kQ2xZ", "router.example.org:40000").is_err());
        assert!(Meet::of("Tr7kQ2xZp4Lm9sWd", "@Rk8mP2qL>198.51.100.9:40000@40000>").is_err());
        assert!(Meet::of("Tr7kQ2xZp4Lm9sWd", "router:abc").is_err());
        assert!(Meet::of("Tr7kQ2xZp4Lm9sWd", "router:+80").is_err());
        assert!(Meet::of("Tr7kQ2xZp4Lm9sW!", "router.example.org").is_err());
        assert!(Meet::of("Tr7kQ2xZp4Lm9sWd ", "router.example.org").is_err());
        assert!(Meet::place("@router.example.org:40000").is_err());
        assert!(Meet::place("=router.example.org:41000").is_err());
        assert!(Meet::place("@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000").is_err());
        assert!(Meet::place("@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000@").is_err());
        assert!(Meet::place(">?Rk8mP2qLx3Vb7NtY>198.51.100.9:40000:41000").is_err());
        assert!(Meet::place("@Rk8mP2qLx3Vb7NtY>198.51.100.9:40000,Hx4nT7wAe2Kq9VsM>s2.example.org:40000@41000").is_err());
    }
}
