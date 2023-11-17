use std::net::{TcpListener, TcpStream};

use simple_https_client::tls13client;
use simple_https_server::tls13server;

#[test]
fn self_test() {
    let (tx, rx) = std::sync::mpsc::channel();

    // Server thread.
    let server = std::thread::spawn(move || {
        let (stream, _) = {
            // We use an ephemeral (free) port (by using ":0") ...
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let port = listener.local_addr().unwrap().port();
            println!("Server listens on 127.0.0.1:{}.", port);

            // ... and let the client thread know.
            tx.send(port).unwrap();

            listener.accept().unwrap()
        };

        tls13server(stream, "127.0.0.1", None).unwrap();

        println!("Server finished.");
    });

    // Client thread.
    let port = rx.recv().unwrap();

    let client = TcpStream::connect(("127.0.0.1", port)).unwrap();

    println!("Client connected to 127.0.0.1:{}.", port);

    let (_, _, data) = tls13client(
        "127.0.0.1",
        client,
        None,
        "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n",
    )
    .unwrap();

    println!("{}", std::str::from_utf8(&data).unwrap());

    println!("Client finished.");

    server.join().unwrap();
}
