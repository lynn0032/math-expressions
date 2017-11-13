var assoc = require("../trees/associate.js");
var trans = require("../trees/basic.js");
var textToAst = require("../parser.js").text.to.ast;
var normalize_negatives = require("../trees/default_order").normalize_negatives;
var tuples = require('./normalization/tuples');

function expand_ast(tree) {
    tree = assoc.deassociate(tree, "*");
    tree = assoc.deassociate(tree, "+");

    transformations = [];
    transformations.push([textToAst("a*(b+c)"), textToAst("a*b+a*c")]);
    transformations.push([textToAst("(a+b)*c"), textToAst("a*c+b*c")]);
    transformations.push([textToAst("-(a+b)"), textToAst("-a-b")]);

    tree = trans.applyAllTransformations(tree, transformations, 20);
    
    tree = assoc.associate(tree, "*");
    tree = assoc.associate(tree, "+");

    tree = normalize_negatives(tree);
    
    return tree;
}

function expand(expr) {
    return expr.context.from(expand_ast(expr.tree));
}

function expand_relations_ast(tree) {
    return trans.transform(tree, expand_relations_transform);
}

function expand_relations_transform (ast) {
    if(!Array.isArray(ast)) {
	return ast;
    }

    var operator = ast[0];
    var operands = ast.slice(1);
    // since transforms in bottom up fashion,
    // operands have already been expanded

    if(operator === '=') {
	if(operands.length <= 2)
	    return ast;
	var result = ['and'];
	for(var i=0; i < operands.length-1; i++) {
	    result.push(['=', operands[i], operands[i+1]]);
	}
	return result;
    }
    if(operator === 'gts' || operator === 'lts') {
	var args = operands[0]
	var strict = operands[1];

	if(args[0] != 'tuple' || strict[0] != 'tuple')
	    // something wrong if args or strict are not tuples
	    throw new Error("Badly formed ast");
	

	var comparisons = []
	for(var i=1; i< args.length-1; i++) {
	    var new_operator;
	    if(strict[i]) {
		if(operator == 'lts')
		    new_operator = '<';
		else
		    new_operator = '>';
	    }
	    else {
		if(operator == 'lts')
		    new_operator = 'le';
		else
		    new_operator = 'ge';
	    }
	    comparisons.push([new_operator, args[i], args[i+1]]);
	}
	
	var result = ['and', comparisons[0], comparisons[1]];
	for(var i=2; i<comparisons.length; i++)
	    result = ['and', result, comparisons[i]];
	return result;
    }

    // convert interval containment to inequalities
    if(operator === 'in' || operator === 'notin' ||
       operator === 'ni' || operator === 'notni') {

	var negate=false;
	if(operator === 'notin' || operator === 'notni')
	    negate=true;

	if(operator === 'in' || operator === 'notin') {
	    var x = operands[0];
	    var interval = operands[1];
	}
	else {
	    var x = operands[1];
	    var interval = operands[0];
	}

	// convert any tuples/arrays of length two to intervals
	interval = tuples._to_intervals_ast(interval);

	// if not interval, don't transform
	if(interval[0] !== 'interval')
	    return ast;

	var args = interval[1];
	var closed = interval[2];
	if(args[0] !== 'tuple' || closed[0] !== 'tuple')
	    throw new Error("Badly formed ast");

	var a = args[1];
	var b = args[2];

	var comparisons = [];
	if(closed[1]) {
	    if(negate)
		comparisons.push(['<', x, a]);
	    else
		comparisons.push(['ge', x, a]);
	}
	else {
	    if(negate)
		comparisons.push(['le', x, a]);
	    else
		comparisons.push(['>', x, a]);
	}
	if(closed[2]) {
	    if(negate)
		comparisons.push(['>', x, b]);
	    else
		comparisons.push(['le', x, b]);
	}
	else {
	    if(negate)
		comparisons.push(['ge', x, b]);
	    else
		comparisons.push(['<', x, b]);
	}

	var result;
	if(negate)
	    result =  ['or'].concat(comparisons);
	else
	    result =  ['and'].concat(comparisons);

	return result;
    }
    
    // convert interval containment to inequalities
    if(operator === 'subset' || operator === 'notsubset' ||
       operator === 'superset' || operator === 'notsuperset') {

	var negate=false;
	if(operator === 'notsubset' || operator === 'notsuperset')
	    negate=true;

	if(operator === 'subset' || operator === 'notsubset') {
	    var small = operands[0];
	    var big = operands[1];
	}
	else {
	    var small = operands[1];
	    var big = operands[0];
	}

	// convert any tuples/arrays of length two to intervals
	small = tuples._to_intervals_ast(small);
	big = tuples._to_intervals_ast(big);

	// if not interval, don't transform
	if(small[0] !== 'interval' || big[0] !== 'interval')
	    return ast;

	var small_args = small[1];
	var small_closed = small[2];
	var big_args = big[1];
	var big_closed = big[2];
	if(small_args[0] !== 'tuple' || small_closed[0] !== 'tuple' ||
	   big_args[0] !== 'tuple' || big_closed[0] !== 'tuple')
	    throw new Error("Badly formed ast");

	var small_a = small_args[1];
	var small_b = small_args[2];
	var big_a = big_args[1];
	var big_b = big_args[2];

	var comparisons = [];
	if(small_closed[1] && !big_closed[1]) {
	    if(negate)
		comparisons.push(['le', small_a,big_a]);
	    else
		comparisons.push(['>', small_a,big_a]);
	}
	else {
	    if(negate)
		comparisons.push(['<', small_a,big_a]);
	    else
		comparisons.push(['ge', small_a,big_a]);
	}
	if(small_closed[2] && !big_closed[2]) {
	    if(negate)
		comparisons.push(['ge', small_b,big_b]);
	    else
		comparisons.push(['<', small_b,big_b]);
	}
	else {
	    if(negate)
		comparisons.push(['>',small_b,big_b]);
	    else
		comparisons.push(['le',small_b,big_b]);
	}
	var result;
	if(negate)
	    result =  ['or'].concat(comparisons);
	else
	    result =  ['and'].concat(comparisons);

	return result;
	
    }

    return ast;
}

function expand_relations(expr) {
    return expr.context.from(expand_relations_ast(expr.tree));
}

exports._expand_ast = expand_ast;
exports._expand_relations_ast = expand_relations_ast;

exports.expand = expand;
exports.expand_relations = expand_relations;