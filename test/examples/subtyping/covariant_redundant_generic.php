<?hh

class Bigly {}
class Smol extends Bigly {}

class Cov<+T> {}

function rcvr<T as Bigly>(Cov<T> $_): null {
    return null;
}

function caller(Cov<Smol> $smol): null {
    return rcvr($smol);
}