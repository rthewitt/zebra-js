/*
 * I intend to create a bipartite graph from variables->values from the hypergraph.
 * Doing so will allow me to find a matching, and satisfy the arc-consistency
 * in regards to the AllDiff constraint.
 */
var _ = require('underscore');

var FAILURE = -1;
var CNST = 0;

////////// DEFINITIONS //////////
var people = ["englishman", "spaniard", "norwegian", "ukrainian", "japanese"];
var pets = ["dog", "zebra", "fox", "snail", "horse" ];
var colors = ["green", "blue", "yellow", "red", "ivory"];
var drinks = ["coffee", "water", "oj", "milk", "tea"];
var candies = ["kit-kat", "smarties", "snickers", "hershey", "milky-way"];

var domain = [1, 2, 3, 4, 5];
var variables = [].concat(people, pets, colors, drinks, candies);



//#############################################
/////// GRAPH DATA STRUCTURE /////////////////
//#############################################

// Attempting to convert to hypergraph
var ConstraintGraph = function (vertices, edges, directed) {
    this.vertices = vertices || [];
    this.edges = edges || [];
    this.directed = directed || false;
};

// separate out into WeightedGraph in library
// TODO require an ID on vertices/edges as a means of key
ConstraintGraph.prototype = {
    vertices: null,
    edges: null,
    directed: false
}

function _generateID () {
      var S4 = function() {
         return (((1+Math.random())*0x10000)|0).toString(16).substring(1);
      };
      return (S4()+S4()+"-"+S4()+"-"+S4()+"-"+S4()+"-"+S4()+S4()+S4());
   }

var Vertex = function(info) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.info = info;
    this.edges = []; // TODO handle removal case
    this.domain = [];
    this.constraints = [];
    this.connections = []; // TODO handle removal case maybe
};

// Change implementation such that constraint _is_ an Edge
Vertex.prototype = {
    id: null,
    connections: null, // a set of unique ids of Edges
    info: null,
    edges: null,
    domain: null,
    constraints: null,
    addAssignment: function(assn) {
        if(!(assn.id in this.connections)) {
            this.connections.push(assn.id);
            this.domain.push(assn);
            this.edges.push(assn);
            //edges.push(assn);
        } else console.warn('Duplicate UUID found in addAssignment');
    },
    addConstraint: function(cnst) {
        if(!(cnst.id in this.connections)) {
            this.connections.push(cnst.id); // is this check redundant?
            this.constraints.push(cnst);
            this.edges.push(cnst);
        }
    }
}

var Edge = {
    from: null,
    to: null,
    weight: null,
    isValidEdge: function() {
        return this.to instanceof Array && this.to.length > 0 && 
            this.from instanceof Array && this.from.length > 0;
    }
};

var UNARY=1, BINARY=2, NARY=3;
var Constraint = function(type, relation, scope) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.scope = scope; // TODO remove this if possible
    this.type = type;
    this.check = function() { 
        var params = Array.prototype.slice.call(arguments);
        return relation.apply(this, params); }
    /*
        function() {
        return relation.apply(this, scope)
    } */
};
Constraint.prototype = Edge;

var Assignment = function(valNode) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.to = [valNode];
    //console.log('pushing '+valNode.info+' with id '+valNode.id+' into new edge');
    //console.log('to length now: '+this.to.length)
}
Assignment.prototype = Edge;

var getConstraint = function(scope, rel, optional) {
    var type = (scope.length > 2 ? NARY : (scope.length < 2 ? UNARY : BINARY));
    var from = scope[0];
    var check = typeof optional === 'undefined' ? rel : rel.apply(null, optional); // we're looking for a closure

    // I was originally using a [ tail | head ] structure for hyperedges, now moving toward [ { node set } ]
    // var to = type === UNARY ? [from] : _.without(scope, from); // Do we really want cycles?
    var to = type === UNARY ? [from] : scope.slice();
    var cnst = new Constraint(type, check, scope);
    cnst.to = to;
    cnst.from = from;
    return cnst;
}


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################

function hasDomainValue(vrb, val) {
    for(var d in vrb.domain) {
        var assn = vrb.domain[d];
        if(assn)
            for(var valNode in assn.to) {
                if(assn.to[valNode].info === val)
                    return true;
            }
    }
    return false;
}

function forceSelection(vrb, val) {
    function relevant(edge) {
        if(edge.to.length !== 1) throw "Assignment has wrong dimentionality";
        return edge.to[0].info === val.info;
    }
    var assignment = _.filter(vrb.domain, relevant);
    if(assignment.length !== 1) throw "Duplicate Domain!";
    var inf = [{
        variable: vrb,
        edges: _.reject(vrb.domain, relevant)
        }];
    vrb.domain = assignment;
    return inf;
}

function queueAffectedNodes(Q, vNode, spent) {
    console.log('CSP was revised - ' + vNode.info + ' as pivot.');
    _.each(vNode.constraints, function(cnst){
        var slot = [cnst];
        var members = _.without(cnst.to, vNode, spent);
        if(members.length > 0) {
            slot.push(_.without(cnst.to, vNode, spent));
            Q.push(slot);
        }
    });
}

// returns in form: [constraint, [args...]]
function initializeQueue(constraints, Q) {
    if(Q instanceof Array)  {
        var arcs = _.map(constraints, function(cnst){
            return [cnst, _.unique(cnst.to.slice())] // TODO understand why there were duplicates.  (Should have been directional)
        });
        Q.push.apply(Q, arcs);
    } else console.error('Bad Q');
}

//#############################################
//// CONSTRAINT DEFINITIONS //////////////////
//#############################################

// function(scope, optional) return boolean

    var SAME = function(a, b) {
        return a.info === b.info;
    }

    // will return a closure
    var VALUE = function(val) {
        return function(a) {
            //debugger;
            return a.info === val;}
    }

    // TEMPORARY
    var RIGHT = function(a, b) {
        return b.info-a.info === 1;
    }
    var NEXT = function(a, b) {
        return Math.abs(b.info-a.info) === 1;
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


function ac3(csp, inferences) {
    var Q = []; 
    initializeQueue(csp.cMap[UNARY], Q);
    initializeQueue(csp.cMap[BINARY], Q);
    //initializeQueue(csp.cMap[NARY], Q);
    
    while(Q.length > 0) {
        console.log("AC3 running...");
        var arc = Q.shift();
        if(typeof arc === undefined) continue; // FIXME avoid pushing undefined arcs
        var v1 = arc[1][0], v2=arc[1][1];

        switch(parseInt(arc[CNST].type)){
            case UNARY:
            case BINARY:
                if(csp.revise(arc[0], inferences, arc[1])) {
                    if(v1.domain.length === 0) 
                        return FAILURE; 
                    queueAffectedNodes(Q, v1, v2);
                }
                break;
            case NARY:
                // TODO implement
                break;
            default:
                break;
        };
    }
    return true;
}



//#############################################
////////// PROBLEM DEFINITION ////////////////
//#############################################
  
var csp = function(variables, domain, constraints) {
    var self = this;
    this.domain = _.map(domain, function(val){return new Vertex(val);});
    this.vMap = {}; // ONLY WORKS WITH STRINGS / UUIDS!!!
    this.numVars = variables.length;
    _.each(variables, function(v){
        self.vMap[v] = new Vertex(v);
    });

    var cMap = {};
    cMap[UNARY] = [];
    cMap[BINARY] = [];
    cMap[NARY] = [];
    this.cMap = cMap; // Later
    
    _.each(constraints, function(cc){
        var params = cc.slice();
        params[0] = _.map(cc[0], function(varName){return self.vMap[varName]}); 
        var cnst = getConstraint.apply(self, params);
        // TODO connect within graph if not already done?
        cMap[cnst.type].push(cnst);
    });


    // before building, we want all variables in vMap, all edges (constraints+assignments)
    this.buildConstraintGraph();

    // TODO sort variables by inspecting constraints
}

csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.vMap, function(node){assignment[node.info]=node});
    var solution = this.backTrack(assignment);
    if(solution !== FAILURE) {
        console.log("Solved!\n");
        printSolution(solution);
    } else console.log("Failed to find a solution");
}

function printSolution(sol) {
    for(var v in sol) {
        console.log(v+': ');
        for(var d in sol[v].domain) {
            console.log(sol[v].domain[d].to[0].info+' ');
        }
    }
}

// binary only????
csp.prototype.revise = function(cnst, inferences, params) {
    var pivotVar = params[0];
    var modified = false;
    // if no value for v2 exists in C(v1,v2), remove v1 from domaim
    _.each(pivotVar.domain, function(assnEdge){
        var found=false;
        var pivotVal = assnEdge.to[0];
        var targetVar = parseInt(cnst.type) === UNARY ? pivotVar : params[1]; // UGLY unary case
        for(var tv in targetVar.domain) {
            var targetVal = targetVar.domain[tv].to[0]; // domain node
            if(cnst.check(pivotVal, targetVal)) { // is ordering preserved?
                //debugger;
                found = true;
                break;
            }
        }
        if(!found) {
            pivotVar.domain = _.without(pivotVar.domain, assnEdge);
            // TODO MAKE THIS MORE COMPACT
            inferences.push({variable: pivotVar, edges: [assnEdge]});
            modified = true;
        }
    });
    return modified;
}

csp.prototype.revert = function(inferences) {
    console.log('REVERTING');
    if(!inferences) return;
    while(inferences.length > 0) {
        var inf = inferences.pop();
        _.each(inf.edges, function(edge){inf.variable.domain.push(edge);});
    }
}

csp.prototype.getMostConstrainedVar = function() {
    var most; // most so far
    for(var name in this.vMap) {
        var variable = this.vMap[name];

        if(!variable instanceof Vertex)  // Debugging only, TODO delete
            continue;

        if(!most || 
                variable.constraints.length > most.constraints.length) 
            most = variable;
    }
    if(most)
        console.log('most: '+most.info +' with '+most.constraints.length+' constraints');
    return (most && most.constraints.length > 1) ? most : null;
}

// In my hypergraph formulation, inferences are simply edges in the
// bipartite variable->value representation
// A "{var = value}" assignment can be represented by its inverse,
// the set of edges removed in order to specify the assignemnt.
// In this way, state reparation is very straightforward.
csp.prototype.backTrack = function(assignment) {
    //debugger;
    var considered = this.getMostConstrainedVar();

    if(considered === null) 
        return assignment;

    //console.log('considering '+considered.info);
    var inferences;

    for(var vn in this.domain) {
        var valNode = this.domain[vn];
        //console.log('valNode.info = '+valNode.info);
        if(hasDomainValue(considered, valNode.info)) {
            // verify boundary conditions
            inferences = forceSelection(considered, valNode);
            //debugger;
            var ret = this.infer(assignment, inferences);
            if(ret !== FAILURE) { // FIXME this is no longer possible, verify return values
                var recur = this.backTrack(assignment);
                if(recur !== FAILURE)
                    return recur;
            } else {
                console.log('about to fail in current iteration:\n');
                //printSolution(assignment);
            }
        }
        // completely revert
        this.revert(inferences); // adds the edges back into the graph
    }
    debugger;
    return FAILURE;
}

csp.prototype.infer = function(assignment, inferences) {
    return ac3.call(null, this, inferences);
}

// Considering reworking inheritance here
csp.prototype.buildConstraintGraph = function() {
    console.log('Building Constraint Graph');
    // vertices: come directly from constraints
    //this.graph = new ConstraintGraph(v,e,d);

    var self = this;
    console.log('Number of unary constraints: '+self.cMap[UNARY].length);
    console.log('Number of binary constraints: '+self.cMap[BINARY].length);
    console.log('Number of nary constraints: '+self.cMap[NARY].length);

    var vertices = [];
    var edges = [];

    _.each(this.vMap, function(varNode){
        vertices.push(varNode); // add to graph collection
        _.each(self.domain, function(valNode){
            var ass = new Assignment(valNode);
            varNode.addAssignment(ass);
        //    edges.push(ass); TODO decide if a single collection is ever worthwhile
        });
    });

    for(var type in this.cMap){
        switch(parseInt(type)) {
            case UNARY:
                break;
            case BINARY:
                _.each(this.cMap[type], function(cc){
                    for(var i=0; i<cc.scope.length; i++) {
                        if(!cc.scope[i]) continue; // I think this has been fixed, DELETE FIXME
                        var vertex = self.vMap[cc.scope[i].info]; // get from the collection
                        cc.to.push(vertex);
                        var others = _.without(cc.scope, vertex.info);
                        _.each(others, function(affected){
                            vertex.addConstraint(cc);
                        });
                        edges.push(cc); // add to graph-global collection
                    }
                });
                break;
            case NARY:
                break;
            default:
                break;
        }
    }

    // NEED VERTICES, EDGES
    var graph = new ConstraintGraph(vertices, edges);
}


var constraints = [
    [ ["englishman", "red"], SAME ],
    [ ["spaniard", "dog"], SAME ],
    [ ["norwegian"], VALUE, [1]],
    [ ["ivory", "green"], RIGHT ],
    [ ["hershey", "fox"], NEXT ],
    [ ["kit-kat", "yellow"], SAME ],
    [ ["norwegian", "blue"], NEXT ],
    [ ["smarties", "snail"], SAME ],
    [ ["snickers", "oj"], SAME ],
    [ ["ukrainian", "tea"], SAME ],
    [ ["japanese", "milky-way"], SAME ],
    [ ["kit-kat", "horse"], NEXT ],
    [ ["coffee", "green"], SAME ],
    [ ["milk"], VALUE, [3]]
];

var problem = new csp(variables, domain, constraints);
problem.solve();
