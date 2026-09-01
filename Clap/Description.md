In the following, we are refering to the values we are constructing (**issuer**, **user id** etc) as "claims" and to the json pairs we are parsing (`iss`, `aud` etc) as "json fields" or "fields".

We represent the set of claims as a stucture containing
- **issuer**, of type string
- **audience**, of type string
- **user id**, of type string
- **issued at**, of type ℕ
- **email verified**, of type bool
- **nonce**, of type string
- **extra field**, of type string

The parser depends on the variables **user id key**, which can be `sub` or `emal` and **extra field key** that can be any string.

In order to construct such a structure, we expect the json string we are parsing to consist of an open bracket '\{' and then all the fields as (key : value) pairs separted by comma, until the closing bracket '\}'. Each such pair has to have the form of a quoted string, followed by ':' character, followed by the value. Depending on the claim that is represented by the json key, we make sure the value has the appropriate form.

- for the **issuer** and **audience**, we use the `iss` and `aud` fields, whose values have to be quoted strings.
- for the **user id**, we use the `sub` or `email` fields, depending on the value of the **user id key** variable. The json value has to be a quoted string.
- for the **issue at** we use the `iat` field, whose value has to be a natural number (whithout quotes).
- for the **email verified** we use the value of the `email_verified` field, it has to be either a string or a bool. If it's a string we make sure it's either "true" or "false"
- for the **nonce** we use the `nonce` field. It has to be a quoted string that contains only digits (also nonempty).
- for the **extra field** we use whatever json field has the key equal to the **extra field key** variable. Its value has to be a quoted string.
- if fields that are not relevant for the claims appear, we ignore them.

If a json string contains two or more fields that share the same key, we generate one result for each of them. For example, if it contains two `iss`s and three `nonce`s, the result will be a list of all six possible claim structures.

- id **user id key** is `email`, then **email verified** has to be true.