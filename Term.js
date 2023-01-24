/*
    Library for representing terms and their
    substitutions. Useful for equational
    reasoning.
*/


/*
    Term Representation
*/


class Variable {
    constructor(name) {
        if (typeof name !== "string") {
            throw Error("Variable name must be a string");
        }
        this.name = name;
    }
    toString() {
        return this.name;
    }
    isEqual(v) {
        return (v instanceof Variable && v.name === this.name);
    }
}

class Constant {
    constructor(name) {
        if (typeof name !== "string") {
            throw Error("Constant name must be a string");
        }
        this.name = name;
    }
    toString() {
        return this.name;
    }
    isEqual(c) {
        return (c instanceof Constant && c.name === this.name);
    }
}

class Func extends Function {
    constructor(name, arity) {
        super('...args', 'return this._bound._call(...args)')

        if (typeof name !== "string") {
            throw Error("Function name must be a string");
        }
        if (!Number.isInteger(arity)) {
            throw Error("Variable arity must be an integer");
        }

        this._bound = this.bind(this)
        this._bound.symbol_name = name;
        this._bound.arity = arity;
        return this._bound
    }

    _call(...args) {
        if (args.length !== this.arity) {
            throw Error("Wrong number of arguments, exected " + this.arity + " received " + args.length);
        }
        return new FuncTerm(new Func(this.symbol_name, this.arity), args);
    }

    toString() {
        return this.symbol_name;
    }
    isEqual(f) {
        return (f instanceof Func && f.symbol_name === this.symbol_name && f.arity == this.arity);
    }
}

function isTerm(t) {
    return (t instanceof Variable) ||
        (t instanceof Constant) ||
        (t instanceof FuncTerm);
}

function zip(a ,b) {
    return a.map((v, i) => [v, b[i]]);
}

class FuncTerm {
    constructor(func, args) {
        if (!(func instanceof Func)) {
            throw Error("First argument must be a Func");
        }
        if (!Array.isArray(args) || !args.every(t => isTerm(t))) {
            throw Error("args must be an array of terms")
        }
        this.func = func;
        this.args = args;
    }
    toString() {
        if (this.func.arity === 0) {
            return this.func.toString();
        }
        return this.func.toString() + "(" + this.args.join(",") + ")";
    }
    isEqual(t) {
        return (t instanceof FuncTerm && zip(this.args, t.args).every(x => x[0].isEqual(x[1])));
    }
}

function cloneTerm(t) {
    if (!isTerm(t)) {
        throw Error("Argument must be of type Term");
    }
    if (t instanceof Variable) {
        return new Variable(t.name);
    }
    if (t instanceof Constant) {
        return new Constant(t.name);
    }
    if (t instanceof FuncTerm) {
        const args = t.args.map(ti => cloneTerm(ti));
        return new FuncTerm(
            new Func(t.func.symbol_name, t.func.arity),
            args
        );
    }
}

class Equation {
    constructor(left_side, right_side) {
        if (!isTerm(left_side)) {
            throw Error("Left side must be a term");
        }
        if (!isTerm(right_side)) {
            throw Error("Right side must be a term");
        }
        this.left_side = left_side;
        this.right_side = right_side;
    }
    toString() {
        return this.left_side.toString() + " = " + this.right_side.toString(); 
    }
}

/*
    Substitutions
*/

class Substitution {
    constructor() {
        this.subs = [];
    }
    toString() {
        const subStrings = this.subs.map(vt => vt[0].toString() + " -> " + vt[1].toString());
        return "{" + subStrings.join(", ") + "}";
    }

}

Substitution.prototype.add = function(variable, term) {
    if (!(variable instanceof Variable)) {
        throw Error("First argument must be a variable");
    }
    if (!isTerm(term)) {
        throw Error("Second argument must be a term");
    }
    if (this.subs.some(vt => vt[0].isEqual(variable))) {
        throw Error("Variable already exists in substitution")
    }
    this.subs.push([variable, term])
}

Substitution.prototype.remove = function(variable) {
    if (!(variable instanceof Variable)) {
        throw Error("Argument must be of type Variable");
    }
    let indexToRemove = -1;
    for (let i = 0; i < this.subs.length; i++) {
        if (this.subs[i][0].isEqual(variable)) {
            indexToRemove = i;
        }
    }
    if (indexToRemove !== -1) {
        this.subs.splice(indexToRemove, 1);
    }
}

Substitution.prototype.apply = function(t) {
    if (!isTerm(t)) {
        throw Error("Argument must be of type Term");
    }

    if (this.subs.length === 0) {
        return cloneTerm(t);   
    }

    if (t instanceof FuncTerm) {
        const args = t.args.map(ti => this.apply(ti));
        return new FuncTerm(
            new Func(t.func.symbol_name, t.func.arity),
            args
        );
    }

    if (t instanceof Variable) {
        for (const [v, tNew] of this.subs) {
            if (v.isEqual(t)) {
                return cloneTerm(tNew);
            }
        }
    }

    return cloneTerm(t);
}

function cloneSubstitution(sub) {
    // Source: Franz Baader and Wayne Snyder.
    // Unification Theory. Handbook of Automated Reasoning, 2001
    if (!(sub instanceof Substitution)) {
        throw Error("Argument must be of type substitution");
    }

    let newSubstitution = new Substitution();

    for (const [v, t] of sub.subs) {
        newSubstitution.add(cloneTerm(v), cloneTerm(t));
    }

    return newSubstitution;
}

Substitution.prototype.contains = function(variable) {
    if (!(variable instanceof Variable)) {
        throw Error("Substitution contains only considers the variables")
    }
    return this.subs.some(vt => vt[0].isEqual(variable))
}

Substitution.prototype.compose = function(sigma) {
    // Source: Franz Baader and Wayne Snyder.
    // Unification Theory. Handbook of Automated Reasoning, 2001
    if (!(sigma instanceof Substitution)) {
        throw Error("Argument must be of type substitution");
    }

    if (this.subs.length == 0) {
        return cloneSubstitution(sigma);
    }

    let newSubstitution = new Substitution();

    // Apply substitution to every term within our current one
    for (const [v, t] of this.subs) {
        newSubstitution.add(
            cloneTerm(v),
            sigma.apply(t)
        );
    }

    // Remove any binding x->t where x in Domain(this)
    let newSigma = cloneSubstitution(sigma);
    for (const [v, t] of newSubstitution.subs) {
        if (newSigma.contains(v)) {
            newSigma.remove(v);
        }
    }

    // Remove trivial bindings
    for (const [v, t] of newSubstitution.subs) {
        if (v.isEqual(t)) {
            newSubstitution.remove(v);
        }
    }

    // Union the two subsitutions
    for (const [v, t] of newSigma.subs) {
        newSubstitution.add(v, t);
    }

    return newSubstitution;
}

if (typeof module !== "undefined" && module.exports) {
    module.exports.Variable = Variable;
    module.exports.Constant = Constant;
    module.exports.Func = Func;
    module.exports.Substitution = Substitution;
    module.exports.Equation = Equation;
}
