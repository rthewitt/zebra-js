var _ = require('underscore');

var FAILURE = -1;

////////// DEFINITIONS //////////
var people = ["englishman", "spaniard", "norwegian", "ukrainian", "japanese"];
var pets = ["dog", "zebra", "fox", "snail", "horse" ];
var colors = ["green", "blue", "yellow", "red", "ivory"];
var drinks = ["coffee", "water", "oj", "milk", "tea"];
var candies = ["kit-kat","smarties","snickers","hersheys","milky-way"];

var domain = [1, 2, 3, 4, 5];
var variables = [].concat(people, pets, colors, drinks, candies);

var UNARY=1, BINARY=2, NARY=3;
function constraint(t, r, s){this.type = t; this.force = r || function(){}; this.scope = s || [];}
var unary = new constraint(UNARY);
var binary = new constraint(BINARY);
var nary = new constraint(NARY);


// ORDER CONSTRAINT ARRAY BY TYPE DURING EXECUTION!!!!!!  


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################

function getConstraint(scope, rel, optional) {
    var c = function(){};
    c.prototype = (scope.length > 2 ? nary : (scope.length < 2 ? unary : binary));
    function f(args) {
        return function(){return rel.apply(this, args)}
    }
    var args = optional || [];
    var constraint = new c();
    constraint.scope = constraint.scope.concat(scope);
    constraint.force = f(scope.concat(args)); // in case unary/nary with arguments
    return constraint;
}

function isAssigned(dom) {
    return dom.length == 1;
}

function getAssigned(vars) {
    return _.chain(vars)
        .filter(isAssigned)
        .flatten().value();
}

//#############################################
//// CONSTRAINT DEFINITIONS //////////////////
//#############################################

// function(scope, optional) return boolean

    var SAME = function(a, b) {
        return a === b;
    }

    var VALUE = function(a, val) {
        return a === val;
    }

    // TEMPORARY
    var RIGHT = function(a, b) {
        return b-a === 1;
    }
    var NEXT = function(a, b) {
        return Math.abs(b-a) === 1;
    }

    // vars is an array of domain arrays!! 
    var ALL_DIFF = function(vars) {
        var modified = false;

        // separate variables already assigned
        var assigned = getAssigned(vars);
        while(assigned.length !== 0) {
            vars = _.chain(vars)
                .reject(isAssigned) // remove them from original
                .map(function(vDomain){
                    console.log("FILTERING: modified was: "+modified); // verify closure behavior
                    var filtered = _.difference(vDomain, assigned);
                    if(filtered.length !== vDomain.length)
                        modified = true; 
                    return filtered;
                }).value();

            assigned = getAssigned(vars); // check again for singletons
        }
        return modified;
    }

//#############################################
////////// ALT. CONSISTENCY ALGORITHMS  //////
//#############################################

function ac3(csp, assignment) {
    var Q = [];
    for(var vertex in csp.graph)
        for(var affected in csp.graph[vertex].neighbors)
            Q.unshift({v1: vertex, v2: affected});

    while(Q.length > 0) {
        var arc = Q.shift();
        if(revise()) {
            if(assignment[arc.v1].length === 0)
                return false;
            var otherNeighbors = _(csp.graph[vertex].neighbors).without(v2);
            for(var possiblyAffected in otherNeighbors) 
                Q.unshift({v1: possiblyAffected, v2: vertex});
        }
    }
}

// TODO change back from assignment
function revise(csp, assignment, v1, v2) {
    var modified = false;
    var found=false;
    // use constraint whose scope is below
    // if no value for v2 exists in C(v1,v2), remove v1 from domaim
    for(var v1Val in assignment[v1]) {
        for(var value in assignment[v2]) {
            
        }
    }
}

/* these variables have not been ported
function revise(a, b) {
    var deleted = false;
    _.each(a.domain, function(value){
        var found = false;
        _each(value, );
    });
}
*/

function getMostConstrainedVar(assignment) { // FIXME just grabs first
    var ret=null;
    for(var variable in assignment) {
        if(assignment[variable].length > 1)
            ret = assignment[variable];
    }
    return ret;
}


//#############################################
////////// PROBLEM DEFINITION ////////////////
//#############################################
  
var csp = function(variables, domain, constraints) {
    this.domain = domain;
    this.variables = variables;
    this.constraints = [];
    var self = this;
    _.each(constraints, function(cc){
        self.constraints.push(getConstraint.apply(self, cc));
    });
    this.buildConstraintGraph();

    console.log('checking graph\n')
    for(var nn in this.graph) {
        console.log('\n'+nn+': '+this.graph[nn].neighbors);
    }
    // sort variables by inspecting constraints
    // for each constraint, for each in scope push unique others in scope
    //this.neighbors = _.map();
}

csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.variables, function(name){assignment[name]=domain.slice();});
    var solution = this.backTrack(assignment);
    if(solution !== FAILURE && solution instanceof Array)
        alert("Solved!\n"+solution);
}

// are all variables assigned?
csp.prototype.isComplete = function(assignment) {
    return getAssigned().length === this.variables.length;
}

csp.prototype.backTrack = function(assignment) {
    console.log(assignment);
    if(this.isComplete(assignment)) return assignment;

    var considered = getMostConstrainedVar(assignment); // FIXME

    console.log('considering '+considered);
    if(considered === null) {
        console.error("Unable to find constrained var, verify state.");
        return FAILURE;
    }

    var snapshot = considered;
    for(var val in this.domain) {
        if(val in considered){
            var inference = {};
            //assignment[considered.name] = _reject();

            // INFERENCE
            this.infer();
            // END INFERENCE

        }
        // completely revert
        //assignment[considered] = snapshot; // FIXME this does not revert inferences!!!!
    }
    return FAILURE;
}

csp.prototype.infer = function() {
    // CHOOSE APPROPRIATE ALGORITHM BASED ON
    // TYPES OF CONSTRAINTS.  POSSIBLE HYBRID SELECTION?
}

csp.prototype.buildConstraintGraph = function() {
    this.graph = this.graph || {};
    var self = this;
    console.log('Number of constraints: '+self.constraints.length);
    _.each(self.constraints, function(cc){
        console.log('Constraint of length: '+cc.scope.length);
        for(var i=0; i<cc.scope.length; i++) {
            var vertex = cc.scope[i];
            var others = _.without(cc.scope, vertex);
            console.log('scope check '+others);
            if(vertex in self.graph)
                self.graph[vertex].neighbors = _(self.graph[vertex].neighbors.concat()).uniq(); // mixed style
            else 
                self.graph[vertex].neighbors = others;
        }
    });
}

var constraints = [
    [ ["englishman", "red"], SAME ],
    [ ["spaniard", "dog"], SAME ],
    [ ["norwegian"], VALUE, 0],
    [ ["ivory", "green"], RIGHT ],
    [ ["hershey", "fox"], NEXT ],
    [ ["kit-kat", "yellow"], SAME ],
    [ ["norwegian", "blue"], NEXT ],
    [ ["smarties", "snail"], SAME ],
    [ ["snickers", "oj"], SAME ],
    [ ["ukrainian", "tea"], SAME ],
    [ ["japanese", "milkey-way"], SAME ],
    [ ["kit-kat", "horse"], NEXT ],
    [ ["coffee", "green"], SAME ],
    [ ["milk"], VALUE, 2]
];


var problem = new csp(variables, domain, constraints);
problem.solve();
