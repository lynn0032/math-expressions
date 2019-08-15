import { get_tree } from '../trees/util';
import * as simplify from '../expression/simplify';
import math from '../mathjs';
import { operators as operators_in } from '../expression/variables';
import { evaluate_to_constant } from '../expression/evaluation';
import * as default_order from '../trees/default_order';
import _ from 'underscore';
import * as polynomial from '../polynomial/polynomial';

function single_var(poly){
    //takes polynomial in terms representation ["polynomial_terms", (highest term, monomial),...,(lowest term, monomial)] returns the variable if the polynomial has only one variable, false otherwise.
    if (!Array.isArray(poly) || poly[0] !== "polynomial_terms")
        return "_true";                //if polynomial is constant, it's single variable.

    let len = poly.length;
    let vars = new Set();
    for (let i = 1; i < len; i = i+1){
        if (Array.isArray(poly[i]) && (poly[i][0] === "monomial")){
            if ((poly[i][2]).length > 1)
                return "_false";
            vars.add(poly[i][2][0][0]);
            var variable = poly[i][2][0][0];
            if (vars.size > 1)
                return "_false";
        }
    }
    return variable;
}

function poly_to_sv(poly, variable){
    //takes a single variable polynomial in terms representation ["polynomial_terms", (highest term, monomial),...,(lowest term, monomial)] with variable given and converts to simpler single variable representation ["sv_poly", var, [[highest deg, coeff],..., [lowest deg, coeff]]]. Should only be called on single variable polynomials.
    if (!Array.isArray(poly) || poly[0] !== "polynomial_terms")
        return poly;                //if polynomial is constant, don't need to convert.

    let len = poly.length;
    let sv = ["sv_poly", variable, []];
    for (let i = 1; i < len; i = i+1){
        if (Array.isArray(poly[i]) && (poly[i][0] === "monomial"))
            (sv[2]).push([poly[i][2][0][1],poly[i][1]]);
        else
            (sv[2]).push([0,poly[i]]);
    }
    return sv;
}

function sv_to_poly(f){
    //takes a single variable polynomial and converts to terms representation.

    if (!Array.isArray(f) || f[0] !== "sv_poly")
        return f;                //if polynomial is constant, don't need to convert.

    let terms = f[2];
    let len = f[2].length;
    let poly = ["polynomial_terms"];
    for (let i = 0; i < len; i = i+1){
        poly.push(["monomial", terms[i][1], [[f[1], terms[i][0]]]]);
    }

    return poly;
}

function sv_deg(poly){
    //takes a single variable polynomial and returns the degree.
    if (!Array.isArray(poly) || poly[0] !== "sv_poly")
        return 0;

    return poly[2][0][0];
}

function int_gcd(a,b){
    while (b){
        var x = b;
        b = a % b;
        a = x;
    }
    return a;
}

function deg_gcd(poly){
    let max = poly[2].length;
    let gcd = poly[2][0][0];
    for (let i = 0; i < max; i = i+1){
        if (poly[2][i][0] !== 0)
            gcd = int_gcd(poly[2][i][0], gcd);
        if (gcd === 1)
            return 1;
    }
    return gcd;
}

function change_var(poly, n){
    //changes the variable of a polynomial from x to x^n, adjusting the degrees to keep the polynomial the same.
    let new_poly = ["polynomial", ['^', poly[1], n], []];
    let max = poly[2].length;
    for (let i = 0; i < max; i = i+1)
        new_poly[2].push([(poly[2][i][0])/n, poly[2][i][1]]);
    return new_poly;
}

function all_factors(n){
    //returns an array of all factors of the integer. This is a potential bottleneck for efficiency.
    let factors = [];
    let max = Math.sqrt(n);
    for (let i = 1; i <= max; i = i+1){
        if (n % i === 0){
            factors.push(i);
            if (i !== max)
                factors.push(n/i);
        }
    }
    return factors;
}

function rational_roots_candidates(poly){
    //takes a single variable polynomial with integer coefficients, and returns all possible rational roots, according to the rational roots theorem.
    let constant_factors = all_factors(Math.abs(poly[2][0][1]));
    let leading_factors = all_factors(Math.abs(poly[2][(poly[2]).length - 1][1]));
    let candidates = [0];
    constant_factors.forEach(function(p){
                             leading_factors.forEach(function(q){
                                        let simplified = simplify.simplify(['/', p, q]);
                                        var contains = candidates.some(elem =>{
                                                                               return JSON.stringify(simplified) === JSON.stringify(elem);
                                                                               });
                                        if (!contains){
                                             candidates.push(simplified);
                                                     }
                                        simplified = simplify.simplify(['/', ['*', -1, p], q]);
                                        contains = candidates.some(elem =>{
                                                                                return JSON.stringify(simplified) === JSON.stringify(elem);
                                                                                });
                                        if (!contains){
                                             candidates.push(simplified);
                                                     }
                                                     });
                             });
    return candidates;
}

function is_root(poly, x){
    if (!Array.isArray(poly) || poly[0] !== "polynomial"){
        return (poly === 0);
    }
    let expression = 0;
    poly[2].forEach(function(term){
        expression = ['+', expression, ['*', term[1], ['^', x, term[0]]]];
        });
    return (simplify.simplify(expression) === 0);
}

function rational_roots(poly){
    //takes a single variable polynomial with rational coeffecients, and returns an array of all rational roots of the polynomial.
    let candidates = rational_roots_candidates(poly);
    let roots = [];
    candidates.forEach(function(x){
                  if (is_root(poly,x))
                        roots.push(x);
                  });
    return roots;
}

function differentiate(poly){
    let terms = [];
    poly[2].forEach(function(term){
                    if (term[0] > 0)
                    terms.push([term[0] - 1, simplify.simplify(['*',term[0],term[1]])]);
                    });
    return ["polynomial", poly[1], terms];
}

function find_multiplicity(poly, root){
    let multiplicity = 0;
    while (is_root(poly,root)){
        multiplicity = multiplicity + 1;
        poly = differentiate(poly);
    }
    return multiplicity;
}

function rational_roots_with_mult(poly){
    let roots = rational_roots(poly);
    let roots_and_mult = [];
    roots.forEach(function(x){
                  roots_and_mult.push([x,find_multiplicity(poly, x)]);
                  });
    return roots_and_mult;
}

function extract_factors(expression){
    let our_tree = expression.tree;
    if (!Array.isArray(our_tree) || our_tree[0] !== '*'){
        var factors = [our_tree];
        return [our_tree];
    } else{
        var factors = our_tree.slice(1);}
    let len = factors.length;
    for (let i = 0; i < len; i = i+1){
        if (Array.isArray(factors[i]) && factors[i][0] === '^'){
            factors[i] = factors[i][1];
        }
    }
    return factors;
}

function can_be_factored_basic(poly){
    if (poly[2][(poly[2]).length - 1][0] === 1)
        return false;
    if ((rational_roots(poly)).length !== 0)
        return true;
    return false;
}

function can_be_factored(expression){
    let poly = polynomial.expression_to_polynomial(expression);
    if (!Array.isArray(poly) || poly[0] !== "polynomial")
        return false;
    let n = deg_gcd(poly);
    let factors = all_factors(n);
    let max = factors.length;
    for (let i = 0; i < max; i = i+1){
        let new_poly = change_var(poly, factors[i]);
        if (can_be_factored_basic(new_poly))
            return true;
    }
    return false;
}

function is_factored(expression){
    let factors = extract_factors(expression);
    let len = factors.length;
    for (let i = 0; i < len; i = i+1){
        if (can_be_factored(factors[i]))
            return false;
    }
    return true;
}

function sv_add(f,g){
    //takes two single variable polynomials in the same variable and returns their sum
    let coeff_sum = 0;

    if (!Array.isArray(g) || g[0] !== "sv_poly"){
        //if g is constant
        if (g === 0){
            return f;
        }

        if (!Array.isArray(f) || f[0] !== "sv_poly"){
            //if f is also constant, return their sum as constants
            return simplify.simplify(['+', f, g]);
        }
        let sum = ["sv_poly", f[1], []];
        let len = (f[2]).length;
        for (let i = 0; i < len-1; i = i+1){
            sum[2].push(f[2][i]);
        }
        let i = len-1;
        if (f[2][i][0] === 0){
            coeff_sum = simplify.simplify(['+', f[2][i][1], g]);
            if (coeff_sum !== 0)
                sum[2].push([0,coeff_sum]);
        }
        else{
            sum[2].push(f[2][i]);
            sum[2].push([0,g]);
        }
        return sum;
    }

    if (!Array.isArray(f) || f[0] !== "sv_poly"){
        //if f is constant
        if (f === 0){
            return g;
        }

        let sum = ["sv_poly", g[1], []];
        let len = g[2].length;
        for (let i = 0; i < len-1; i = i+1){
                sum[2].push(g[2][i]);
        }
        let i = len-1;
        if (g[2][i][0] === 0){
            coeff_sum = simplify.simplify(['+', f, g[2][i][1]]);
            if (coeff_sum !== 0)
                sum[2].push([0,coeff_sum]);
        }
        else{
            sum[2].push(g[2][i]);
            sum[2].push([0,f]);
        }
        return sum;
    }

    let sum = ["sv_poly", f[1], []];
    let len_f = f[2].length;
    let len_g = g[2].length;
    let i = 0;
    let j = 0;
    while (i < len_f && j < len_g){
        if (f[2][i][0] > g[2][j][0]){
            sum[2].push(f[2][i]);
            i = i+1;
        }
        else if (f[2][i][0] < g[2][j][0]){
            sum[2].push(g[2][j]);
            j = j+1;
        }
        else{
            coeff_sum = simplify.simplify(['+', f[2][i][1], g[2][j][1]]);
            if (coeff_sum !== 0)
                sum[2].push([f[2][i][0], coeff_sum]);
            i = i+1;
            j = j+1;
        }
    }

    while (i < len_f){
        sum[2].push(f[2][i]);
        i = i+1;
    }

    while (j < len_g){
        sum[2].push(g[2][j]);
        j = j+1;
    }

    if (sum[2].length === 0)
        return 0;

    if (sum[2][0][0] === 0)
        return sum[2][0][1];        //if there's only a constant left, return it as a constant

    return sum;
}

function sv_neg(f){
    //takes a single variable polynomial and returns its negation

    if (!Array.isArray(f) || f[0] !== "sv_poly")
        return simplify.simplify(['-', f]);

    let neg_f = ["sv_poly", f[1], []];
    let len = f[2].length;
    for (let i = 0; i < len; i = i+1){
        neg_f[2].push([f[2][i][0], simplify.simplify(['-', f[2][i][1]])]);
    }

    return neg_f;
}

function sv_sub(f,g){
    //takes a single variable polynomial and returns the difference f-g

    return sv_add(f, sv_neg(g));
}

function sv_mul(f,g){
    //takes two single variable polynomials and returns their product

    if (!Array.isArray(f) || f[0] !== "sv_poly"){
        if (f === 1){
            return g;
        }

        if (f === 0){
            return 0;
        }

        if (!Array.isArray(g) || g[0] !== "sv_poly"){
            return simplify.simplify(['*', f, g]);
        }
        let prod = ["sv_poly", g[1], []];
        let len = g[2].length;
        for (let i = 0; i < len; i = i+1){
            prod[2].push([g[2][i][0], simplify.simplify(['*', g[2][i][1], f])]);
        }
        return prod;
    }

    if (!Array.isArray(g) || g[0] !== "sv_poly"){
        if (g === 1){
            return f;
        }

        if (g === 0){
            return 0;
        }

        let prod = ["sv_poly", f[1], []];
        let len = f[2].length;
        for (let i = 0; i < len; i = i+1){
            prod[2].push([f[2][i][0], simplify.simplify(['*', f[2][i][1], g])]);
        }
        return prod;
    }

    let terms = [];
    let len_f = f[2].length;
    let len_g = g[2].length;
    for (let i = 0; i < len_f; i = i+1){
        for (let j = 0; j < len_g; j = j+1){
            terms.push([f[2][i][0] + g[2][j][0], simplify.simplify(['*', f[2][i][1], g[2][j][1]])]);
        }
    }

    terms.sort(function(a, b){return b[0] - a[0]});

    let combined = [terms[0]];
    let end = 0;
    let coeff_sum = 0;
    let len = terms.length;
    for (let i = 1; i < len; i = i+1){
        end = combined.length-1;
        if (terms[i][0] === combined[end][0]){
            coeff_sum = simplify.simplify(['+', combined[end][1], terms[i][1]])
            if (coeff_sum !== 0)
                combined[end][1] = coeff_sum;
            else
                combined.pop();
        }
        else
            combined.push(terms[i]);
    }

    return ["sv_poly", f[1], combined];
}

function sv_leading(f){
    if (!Array.isArray(f) || f[0] !== "sv_poly")
        return f;
    return ["sv_poly", f[1], [f[2][0]]];
}

function sv_div_lt(term1, term2){
    if (!Array.isArray(term2) || term2[0] !== "sv_poly"){
        if (!Array.isArray(term1) || term1[0] !== "sv_poly")
            return simplify.simplify(['/', term1, term2]);
        let coeff_ratio = simplify.simplify(['/', term1[2][0][1], term2]);
        return ["sv_poly", term1[1], [[term1[2][0][0], coeff_ratio]]];
    }

    if (!Array.isArray(term1) || term1[0] !== "sv_poly")
        return undefined;

    if (sv_deg(term1) < sv_deg(term2))
        return undefined;

    let coeff_ratio = simplify.simplify(['/', term1[2][0][1], term2[2][0][1]]);
    let deg = term1[2][0][0]-term2[2][0][0];

    if (deg === 0)
        return coeff_ratio;

    return ["sv_poly", term1[1], [[deg, coeff_ratio]]];
}

function sv_div(f,g){
    //takes single variable polynomials f,g and returns quotient and remainder [q,r] such that f = gq+r, and deg(r) < deg(g) or r=0.

    let q = 0;
    let r = f;
    let div_lt = 0;
    while (r !== 0 && (sv_deg(g) <= sv_deg(r))){
        div_lt = sv_div_lt(sv_leading(r), sv_leading(g));
        q = sv_add(q, div_lt);
        r = sv_sub(r, sv_mul(div_lt, g));
    }

    return [q,r];
}

function sv_gcd(f,g){
    //takes single variable polynomials f,g and returns their gcd as a single variable polynomial.

    let h = f;
    let s = g;
    let rem = 0;

    while (s !== 0){
        rem = sv_div(h,s)[1];
        h = s;
        s = rem;
    }

    if (!Array.isArray(h) || h[0] !== "sv_poly")
        return 1;           //if gcd is constant, return 1

    let leading_coeff = h[2][0][1];
    return sv_div(h, leading_coeff)[0];
}

function sv_reduce_rational(top, bottom){
    let gcd = gcd(top, bottom);

    if (!Array.isArray(bottom) || bottom[0] !== "sv_poly")
        var bottom_coeff = bottom;           //if gcd is constant, return 1
    else
        var bottom_coeff = bottom[2][0][1];

    let divisor = sv_mul(bottom_coeff, gcd);            //we make the leading coefficient of the bottom 1 in order to standardize the form of the rational expression.
    let new_top = sv_div(top, divisor)[0];
    let new_bottom = sv_div(bottom, divisor)[0];

    return [new_top, new_bottom];
}



export { single_var, poly_to_sv, sv_to_poly, sv_add, sv_neg, sv_sub, sv_mul, sv_leading, sv_div_lt, sv_div, sv_gcd , rational_roots_candidates, all_factors, rational_roots, rational_roots_with_mult, is_factored, extract_factors, can_be_factored };
