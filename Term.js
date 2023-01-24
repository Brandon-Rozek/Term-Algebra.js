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
}

class Func {
    constructor(name, arity) {
        if (typeof name !== "string") {
            throw Error("Function name must be a string");
        }
        if (!Number.isInteger(arity)) {
            throw Error("Variable arity must be an integer");
        }
        this.name = name;
        this.arity = arity;
    }
    call(...args) {
        return FuncTerm(Func(this.name), args);
    }
    toString() {
        return this.name;
    }
}

function isTerm(t) {
    return (t instanceof Variable) ||
        (t instanceof Constant) ||
        (t instanceof FuncTerm);
}

class FuncTerm {
    constructor(func, args) {
        if (!(func instanceof Func)) {
            throw Error("First argument must be a Func");
        }
        if (!Array.isArray(args) || !args.every(t => isTerm(t))) {
            throw Error("args must be an array of terms")
        }
        this.function = func;
        this.arguments = args;
    }
    toString() {
        if (this.arity === 0) {
            return this.function.toString();
        }
        return this.function.toString() + "(" + this.arguments.join(",") + ")";
    }
}

function cloneTerm(t) {
    if (!isTerm(t)) {
        throw Error("Argument must be of type Term");
    }
    if (t instanceof Variable) {
        return Variable(t.name);
    }
    if (t instanceof Constant) {
        return Constant(t.name);
    }
    if (t instanceof FuncTerm) {
        const args = t.args.map(ti => cloneTerm(ti));
        return FuncTerm(t.name, args);
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
        this.subs = {};
    }
    toString() {
        const subStrings = Object.entries(this.subs).map(v, t => v.toString() + " -> " + t.toString());
        return "{" + subStrings.join(",") + "}";
    }

}

Substitution.prototype.add = function(variable, term) {
    if (!(variable instanceof Variable)) {
        throw Error("First argument must be a variable");
    }
    if (!isTerm(term)) {
        throw Error("Second argument must be a term");
    }
    tihs.subs[variable] = term;
}

Substitution.prototype.remove = function(variable) {
    if (!(variable instanceof Variable)) {
        throw Error("Argument must be of type Variable");
    }
    delete this.subs[variable];
}

Substitution.prototype.apply = function(t) {
    if (!isTerm(t)) {
        throw Error("Argument must be of type Term");
    }

    if (Object.keys(this.subs).length == 0) {
        return cloneTerm(t);   
    }

    if (t instanceof FuncTerm) {
        const args = t.args.map(ti => this.apply(ti));
        return FuncTerm(t.name, args);
    }

    if (t instanceof Variable) {
        return cloneTerm(this.subs[t]);
    }

    return cloneTerm(t);
}

function cloneSubstitution(sub) {
    // Source: Franz Baader and Wayne Snyder.
    // Unification Theory. Handbook of Automated Reasoning, 2001
    if (!(sub instanceof Substitution)) {
        throw Error("Argument must be of type substitution");
    }

    let newSubstitution = Substitution();

    for (const [v, t] of Object.entries(sub)) {
        newSubstitution.add(cloneTerm(v), cloneTerm(t));
    }

    return newSubstitution;
}

Substitution.prototype.compose = function(sub) {
    // Source: Franz Baader and Wayne Snyder.
    // Unification Theory. Handbook of Automated Reasoning, 2001
    if (!(sub instanceof Substitution)) {
        throw Error("Argument must be of type substitution");
    }

    if (Object.keys(this.subs).length == 0) {
        return cloneSubstitution(sub);
    }

    let newSubstitution = Substitution();

    // Apply substitution to every term within our current one
    for (const [v, t] of Object.entries(this.sub)) {
        newSubstitution.add(
            cloneTerm(v),
            sub.apply(t)
        );
    }

    // Remove any binding x->t where x in Domain(this)
    let newSubArg = cloneSubstitution(sub);
    for (const v of Object.keys(newSubstitution.subs)) {
        if (Object.keys(newSubArg.subs).contains(v)) {
            newSubArg.remove(v);
        }
    }

    // Remove trivial bindings
    for (const [v, t] of Object.entries(this.sub)) {
        if (v == t) {
            newSubstitution.remove(v);
        }
    }

    // Union the two subsitutions
    for (const [v, t] of Object.entries(newSubArg)) {
        newSubstitution.add(v, t);
    }

    return newSubstitution;
}

if (typeof module !== "undefined" && module.exports) {
    module.exports = [Variable, Constant, Func, Substitution, Equation];
}
