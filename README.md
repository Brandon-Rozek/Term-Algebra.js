# Term-Algebra.js

Terms and substitions for equational reasoning.

To load it in:
```javascript
const Term = require('Term-Algebra');
```

From there you can create terms:
```javascript
// First argument name, second argument arity
f = new Term.Func("f", 1);
g = new Term.Func("g", 2);

x = new Term.Variable("x");
y = new Term.Variable("y");

a = new Term.Constant("a");
b = new Term.Constant("b");
c = new Term.Constant("c");
```

You can create substitutions which are mappings between variables and terms.
```javascript
sigma1 = new Term.Substitution();
sigma1.add(x, g(y, c));

sigma2 = new Term.Substitution();
sigma2.add(y, a);
```


You can compose both substitutions
```javascript
sigma3 = sigma1.compose(sigma2);
console.log(sigma3.toString());
// Returns '{x -> g(a,c), y -> a}'
```

You can apply a substitution to a term
```javascript
console.log(sigma3.apply(f(x)));
// Returns 'f(g(a, c))'
```