module AboutAlma

sig Person {}

sig SoapOpera {
  cast : set Person,    -- a set of "Person"
  alma : cast,
  loves : cast -> cast  -- a relation of "loves" of type "cast" -> "cast"
}

-- Assertion "OfLovers" in a scope of at most two persons and at most one soap opera
-- "all x : T | F" states that formula "F" is true for all instances x of type T
assert OfLovers {
  all S : SoapOpera |
    all x, y : S.cast |
      S.alma in x.(S.loves) && x in y.(S.loves) => not S.alma in y.(S.loves)
}

fact NoSelfLove {
  all S : SoapOpera, p : S.cast |
    not p in p.(S.loves)
} check OfLovers for 3 but 1 SoapOpera
