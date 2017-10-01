
function AJAXGetRequest(file, getstr, callback) {
    var xhr = new XMLHttpRequest();
    // xhr.withCredentails = true;
    if (getstr != '') {
        var s = file + '?' + getstr;
    } else {
        s = file;
    }
    xhr.open("GET", s, true);
    xhr.onreadystatechange = function() {
        if ((xhr.readyState == 4) && (xhr.status == "200")) {
            callback(xhr.responseText);
        }
    }
    xhr.send(null);
}

function AJAXPostRequest(file, fD, callback) {
    var xhttp = new XMLHttpRequest();
    // xhttp.withCredentails = true;
    xhttp.open("POST", file, true);
    xhttp.onreadystatechange = function() {
        if ((xhttp.readyState == 4) && (xhttp.status == "200")) {
            callback(xhttp.responseText);
        }
    }
    xhttp.send(fD);
}
