#!/usr/bin/env python3

import ssl

hostnames = open("top1m.txt", "r")
port = 443

count = 0
counter = 0
print("Getting certificates ...")
for hostname in hostnames:
    hostname = hostname.rstrip()
    print(str(count) + " - " + hostname)
    if counter >= 150:
        print("Got %d certificates out of the top %d" % (count, counter))
        exit(0)
    counter += 1
    try:
        cert = ssl.get_server_certificate((hostname, port))
        f = open('certs/'+hostname+'.der', 'wb')
        f.write(ssl.PEM_cert_to_DER_cert(cert))
        count += 1
        if count >= 1_00:
            break
    except:
        # print("Error getting cert from "+hostname)
        pass
