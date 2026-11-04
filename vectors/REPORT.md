# Прогон Lean-модели на векторах AAT-02

Набор: `vectors/upstream/aat-jws-vectors.json` (229 векторов).
В зоне модели: **177**; совпало **177 из 177**.
Состояние σ после вызова (PoP `jti`) сверено на 3 векторах: совпало 3.

## В зоне модели по ожидаемому шагу

| Ожидается | Шаг | Векторов |
|---|---|---|
| DENY | 1 | 1 |
| DENY | 2c | 1 |
| DENY | 3b | 2 |
| DENY | 3c | 1 |
| DENY | 3d | 1 |
| DENY | 3e | 1 |
| DENY | 3f | 1 |
| DENY | 3g | 1 |
| DENY | 3h | 1 |
| DENY | 3i | 1 |
| DENY | 3k | 2 |
| DENY | 3n | 17 |
| DENY | 4b | 2 |
| DENY | 4c | 1 |
| DENY | 4d | 2 |
| DENY | 4e | 1 |
| DENY | 4g | 1 |
| DENY | 4h | 1 |
| DENY | 4i | 1 |
| DENY | 4j | 1 |
| DENY | 4k | 1 |
| DENY | 4l | 1 |
| DENY | 4m | 1 |
| DENY | 4o | 2 |
| DENY | 4p1 | 1 |
| DENY | 4p2 | 6 |
| DENY | 4p3 | 1 |
| DENY | 4p4 | 24 |
| DENY | 4q | 2 |
| DENY | 6b | 24 |
| DENY | 6c | 4 |
| DENY | 7b | 1 |
| DENY | 7c | 4 |
| DENY | 7d | 3 |
| DENY | 7e | 1 |
| DENY | 7f | 2 |
| DENY | 7g | 2 |
| DENY | 7h | 2 |
| DENY | 7i | 1 |
| PERMIT | — | 54 |

## Расхождения

Нет.

## Вне зоны модели

| Причина | Векторов |
|---|---|
| expected step 3a not modeled | 6 |
| precondition: inadmissible number (assumption 6) | 5 |
| expected step 4n not modeled | 5 |
| expected step 7a not modeled | 4 |
| expected step 3m not modeled | 4 |
| expected step 4a not modeled | 3 |
| precondition: duplicate JSON member names in claims (assumption 7) | 3 |
| expected step 4b2 not modeled | 3 |
| expected step 4b5 not modeled | 3 |
| expected step 3l not modeled | 2 |
| precondition: del_max_depth is not an integer (parsing, 3b/4b) | 2 |
| expected step 4b4 not modeled | 2 |
| precondition: PoP iat is not a NumericDate (parsing, 7c) | 1 |
| precondition: del_depth is not an integer (parsing, 3b/4b) | 1 |
| precondition: exp is not an integer (parsing, 3b/4b) | 1 |
| undecodable: KeyError | 1 |
| expected step 3j not modeled | 1 |
| expected step 2a not modeled | 1 |
| expected step 2b not modeled | 1 |
| precondition: jti missing (3j/4b1) | 1 |
| expected step 4b1 not modeled | 1 |
| expected step 4b3 not modeled | 1 |
