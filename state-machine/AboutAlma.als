// Project over SoapOpera

module AboutAlma

sig Person {}

sig SoapOpera {
  cast : set Person,
  alma : cast,
  loves : cast -> cast
}
assert OfLovers {
  all S : SoapOpera |
  all x, y : S.cast |
        S.alma in x.(S.loves) && x in y.(S.loves) => not S.alma in y.(S.loves)
}

fact NoSelfLove {
  all S : SoapOpera, p : S.cast |
  not p in p.(S.loves)
  }

check OfLovers for 3 but 1 SoapOpera
