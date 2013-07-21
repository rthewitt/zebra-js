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


var GLOBAL = {};

//#############################################
/////// GRAPH DATA STRUCTURE /////////////////
//#############################################

var Vertex = function(info) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.info = info;
    this.domain = [];
    this.constraints = [];
    this.connections = []; // TODO handle removal case maybe
};

// Change implementation such that constraint _is_ an Edge
Vertex.prototype = {
    id: null,
    connections: null, // a set of unique ids of Edges
    info: null,
    domain: null,
    constraints: null,
    addAssignment: function(assn) {
        if(!(assn.id in this.connections)) {
            this.connections.push(assn.id);
            this.domain.push(assn);
        } else console.warn('Duplicate UUID found in addAssignment');
    },
    addConstraint: function(cnst) {
        if(!(cnst.id in this.connections)) {
            this.connections.push(cnst.id); // is this check redundant?
            this.constraints.push(cnst);
        }
    }
}

var Edge = function(from, to, capacity) {
    this.from = from || null;
    this.to = to || null;
    this.capacity = capacity || 1;
    this.isValidEdge = function() {
        return this.to instanceof Array && this.to.length > 0 && 
            this.from instanceof Array && this.from.length > 0;
    }
};

var UNARY=1, BINARY=2, NARY=3;
// if graph ever becomes dynamic, we'll need to manage scope or rely on traversal
// to determine variable dependence.  (Preferred)
var Constraint = function(type, relation, scope) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.scope = scope;  
    this.type = type;
    this.check = function() { 
        var params = Array.prototype.slice.call(arguments);
        return relation.apply(this, params);
    }
};
Constraint.prototype = new Edge();
Constraint.prototype.constructor = Constraint;

var Assignment = function(from, valNode, capacity) {
    Edge.call(this, from, [valNode], capacity);
    this.id = _generateID(); // HANDLE COLLISIONS
};
Assignment.prototype = new Edge();
Assignment.prototype.constructor = Assignment;

var Graph = function(v, e, d) {
    this.vIndex = []; // compare performance of single map
    this.vertices = v || [];
    
    this.edges = e || [];
    this.adj = {};
    this.connections = [];
    this.directed = d || false;
    this.addVertex = function(v) {
        if(!(v.id in this.vIndex)) {
            this.vertices.push(v);
            this.vIndex.push(v.id);
        }
    }
    this.addEdge = function(e) {
        if(!(e.id in this.connections)) {
            this.connections.push(e.id);
            this.edges.push(e);
            if(e.from) {
                if(e.from.id in this.adj)
                    this.adj[e.from.id].push(e);
                else this.adj[e.from.id] = [ e ];
            }
        }
    };
    this.refreshIndex = function() {
        this.connections = [];
        for(var e=0; e<this.edges.length; e++)
            this.connections.push(this.edges[e].id);
        for(var e in this.adj) {
            this.adj[e] = _.filter(this.edges, function(edge) {
                return edge.from.id === e || edge.to[0].id === e; // Ugly specific hack
            });
        }
    }

    // ensures index if constructor accepted arrays. Unique NOT enforced!
    var graph = this;
    _.each(this.vertices, function(v){graph.addVertex(v);});
    _.each(this.edges, function(e){graph.addEdge(e);});
}
var tmpGraph = function(){};
tmpGraph.prototype = Graph.prototype;

// TODO add constraints/variables as array, for sorting purposes?
// (currently using map on csp object)
var ConstraintGraph = function (vertices, directed) {
    Graph.call(this, vertices, null, directed);
};
ConstraintGraph.prototype = new tmpGraph();
ConstraintGraph.prototype.constructor = ConstraintGraph;

var BipartiteFlowGraph = function(source, reversedSink) {
    //console.log('reverse links: '+reversedSink.domain.length);

    Graph.call(this, null, null); 
    this.source = source;
    this.sink = reversedSink; // reminder to fix it first
    this.flow = {};
    this.clean = []; // will house edges that should be removed later
    this.matching = [];

    var self = this;

    function initializeFlow (flush) {
        this.flow = this.flow || {};
        var graph = this;
        _.each(this.edges, function(edge) {
            edge.flow = edge.flow && !flush ? edge.flow : 0;
            graph.flow[edge.id] = edge.flow;
        });
    };

    function integrateNode(node, follow) {
        _.each(node.domain, function(edge) {
            var destNode = edge.to[0];

            // We are passing in a sink connected to domain,
            // so we have to reverse our logic. (Assignment inheritance not working)
            var redge = new Assignment(destNode, edge.from, 0);
            if(node === self.sink) {
                edge.capacity = 0;
                redge.capacity = 1;
            } else redge.capacity = 0;
    
            edge.redge = redge;
            redge.redge = edge;

            //destNode.addAssignment(redge);
    
            self.addEdge(edge);
            self.addEdge(redge);

            // Set graph up to gracefully decompose later
            if(node.info === self.sink.info || node.info === self.source.info) {
                self.clean.push(edge);
            }
            self.clean.push(redge);

            self.addVertex(destNode);

            if(follow) integrateNode(destNode, false);
        });
    }

    integrateNode.call(this, source, true);
    integrateNode.call(this, reversedSink);
    initializeFlow.call(this, true);

    this.flush = function() { 
        return initializeFlow(true);
    };

    // Gracefully degrade to bipartite with matching bidirectionality
    this.demote = function() {
        var self = this;
        // We need to make sure not to eliminate return paths from maximal matching
        if(typeof this.matching != undefined &&
                this.matching instanceof Array) {
            var returnPaths = _.map(self.matching, function(match){return match.redge});
            this.clean = _.difference(self.clean, returnPaths);
        }

        _.each(this.edges, function(e){
            delete e.flow;
            delete e.redge;
        });
        this.edges = _.difference(this.edges, this.clean);
        this.refreshIndex();
    };

    this.getStrongComponents =  function() {
        return getStrongComponents.call(this);
    }

    this.maxFlow = function(source, sink) {
        var self = this;
        this.matching = [];
        var path = this.findPath(source, sink, []);

        // path in form [{ edge: edge, res: residualFlow }, ...]
        while(path) {
            // I think this will work as a min function
            var minFlow = _.reduce(path, function(minFlow, step){
               return step.res < minFlow ? step.res : minFlow;
            }, Infinity);

            // Merge path flow into graph - this blocks when unit flow is capacity!
            _.each(path, function(step){
                self.flow[step.edge.id] += minFlow;
                self.flow[step.edge.redge.id] -= minFlow;
            });

            path = this.findPath(source, sink, []);
        }

        return _.chain(this.adj[source.id])
            .map(function(link){ return self.adj[link.to[0].id]; })
            .flatten(true) // shallow
            .filter(function(link){ return link.to[0].info !== self.sink.info && self.flow[link.id] > 0; })
            .map(function(matchingEdge){
                self.matching.push(matchingEdge);
                return self.flow[matchingEdge.id]; // side-effect!!!
            })
            .reduce(function(sum, f){ 
                return f > 0 ? f+sum : sum; }, 0)
            .value();
    };

    this.findPath = function (src, dst, path) {
        if(src === dst || src.id === dst.id) 
            return path;

        var edj = this.adj[src.id];
        for(var i = 0; i < edj.length; i++) {
            var edge = edj[i];
            var residual = edge.capacity - this.flow[edge.id];  // Equivalent to edge weight

            var inPath = false;
            _.each(path, function(step){
                if(step.edge.id === edge.id)
                    inPath = true;
            });

            if(residual > 0 && !inPath) {
                var newPath = path.concat([{ edge: edge, res: residual }]);
                var result = this.findPath(edge.to[0], dst, newPath);
                if(result)
                    return result;
            }
        }
    };
}
BipartiteFlowGraph.prototype = new tmpGraph();
BipartiteFlowGraph.prototype.constructor = BipartiteFlowGraph;


var getConstraint = function(scope, rel, optional) {
    var type = (scope.length > 2 ? NARY : (scope.length < 2 ? UNARY : BINARY));
    var from = scope[0]; // is this ever used?

    var check;
    var opt = typeof optional;
    if(opt === 'undefined' || opt === 'function')
        check = rel;
    else
        check = optional instanceof Array ? rel.apply(null, optional) : rel.call(null, optional);

    //var check = typeof optional === 'undefined' ? rel : rel.apply(null, optional); // we're looking for a closure

    // to is set in hypergraph, head in directed domain subgraph
    var to = type === UNARY ? [from] : scope.slice();
    var cnst = new Constraint(type, check, scope);
    cnst.to = to;
    cnst.from = from;

    if(opt === 'function') cnst.global = optional;

    return cnst;
}


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################

/* The general strategy for my ALL-DIFF is as follows:
 * Construct Bipartite Graph
 * Use flow theory to fail early on sub-perfect maximal
 * Use Hopcroft-Karp to find perfect matching 
 * Decompose graph into strongly connected components
 * Prune edges by removing component-bridges
**/

// The r-edges from sink->domain COULD in theory be re-used
var buildMatchingGraph = function(vars) {
    // There is a hack that says k-regular MUST have perfect matching
    // If I take advantage of that, can I still prune?

    function pv() {
        var restr="\n";
        for(var vi=0; vi<vars.length; vi++ ) {
            restr+=vars[vi].info+": ";
            for(var di=0; di < vars[vi].domain.length; di++) {
                restr += vars[vi].domain[di].to[0].info+"\n";
            }
        }
        //console.log(restr);
    }

    var source = new Vertex(null);
    var sink = new Vertex(null);

    var sunkenDomain = {};
    _.each(vars, function(rangeNode) {
        source.addAssignment(new Assignment(source, rangeNode));
        _.each(rangeNode.domain, function(domAssn) {
            var domNode = domAssn.to[0];
            if(!(domNode.id in sunkenDomain)) {
                var redge = new Assignment(sink, domNode);
                sink.addAssignment(redge);
                sunkenDomain[domNode.id] = true;
            }
        });
    });
    return  new BipartiteFlowGraph(source, sink);
}

// This function will be called in the context of the Bipartite Graph
function getStrongComponents() {
    var graph = this;

    var uglyHackMap = {}; // TODO remove this collection

    var dpfIndex = {};
    var dpfStack = [];
    var index = 0;

    var components = [];

    for(var idx in this.vertices) {
        var v = this.vertices[idx];
        if(!(v.id in dpfIndex))
            strongConnect(v)
    }
    
    function strongConnect(v) {
        var statV = {};
        statV.index = index;
        statV.lowlink = index++;
        dpfIndex[v.id] = statV;
        if(!uglyHackMap[v.id]) uglyHackMap[v.id] = v; // TODO move into graph
        dpfStack.push(v.id); // TODO I may be able to just push the vertex directly

        _.each(graph.adj[v.id], function(edge) {
            var w = edge.to[0]; // successor node
            if(!(w.id in dpfIndex)) {
                strongConnect(w);
                statV.lowlink = Math.min(statV.lowlink, dpfIndex[w.id].lowlink);
            } else if(dpfStack.indexOf(w.id) !== -1) // the domain node is in the stack, which means it's in the current SCC
                statV.lowlink = Math.min(statV.lowlink, dpfIndex[w.id].index);
        });

        // if v is a root node, pop the stack and generate a component
        if(statV.lowlink === statV.index) {
            var scc = [];
            do {
                var p = dpfStack.pop(); // id of previously pushed node
                scc.push(p);
            } while(p !== v.id);
            components.push(scc);
        }
    }

    return components;
}

function _generateID () {
      var S4 = function() {
         return (((1+Math.random())*0x10000)|0).toString(16).substring(1);
      };
      return (S4()+S4()+"-"+S4()+"-"+S4()+"-"+S4()+"-"+S4()+S4()+S4());
}

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

//function queueAffectedNodes(Q, vNode, spent) {
//  now expect second argument to be array with pivot in first place
function queueAffectedNodes(Q, group) {
    if(group.length > 0) {
        //console.log('CSP was revised - ' + group[0].info + ' as pivot.');
        _.each(group[0].constraints, function(cnst){
            var members = _.difference(cnst.to, group);
            if(members.length > 0) {
                console.log('PUSHING CONSTRAINT t='+parseInt(cnst.type)+' with '+members.length+' NODES ONTO QUEUE');
                var slot = [cnst];
                slot.push(members);
                Q.push(slot);
            }
        });
    }
}

// returns in form: [constraint, [args...]]
function initializeQueue(constraints, Q) {
    if(Q instanceof Array)  {
        var arcs = _.map(constraints, function(cnst){
            return [cnst, _.unique(cnst.to.slice())] // PROBLEM, EXPANDING ABOVE
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
    var OLD_ALL_DIFF = function(vars) {
        var modified = false;

        // separate variables already assigned
        var assigned = getAssigned(vars);
        while(assigned.length !== 0) {
            vars = _.chain(vars)
                .reject(isAssigned) // remove them from original
                .map(function(vDomain){
                    //console.log("FILTERING: modified was: "+modified); // verify closure behavior
                    var filtered = _.difference(vDomain, assigned);
                    if(filtered.length !== vDomain.length)
                        modified = true; 
                    return filtered;
                }).value();

            assigned = getAssigned(vars); // check again for singletons
        }
        return modified;
    } 

    var ALL_DIFF = function(vars, passed) {
        var flowGraph = buildMatchingGraph(vars);
        var maxFlow = flowGraph.maxFlow(flowGraph.source, flowGraph.sink);  // TODO add wrapper function to graph
        flowGraph.demote(); // rename

        passed.push(flowGraph); // optionally hand back arguments for custom revision function

        //console.log('flow from constraint: '+maxFlow);
        return maxFlow == vars.length; // perfect matching exists
    }


    GLOBAL['ALLDIFF_REVISE'] = function(flowGraph, inferences) {
        if(!flowGraph || !inferences) return [];

        var components = flowGraph.getStrongComponents(); // rename
        
        var notInMatching = _.difference(this.edges, this.matching);

        var inf = _.chain(notInMatching)
            .map(function(match) {

                var comp;
                for(var x in components)
                    if(components[x].indexOf(match.from.id) != -1)
                        comp = components[x];

                var deadEnd = [];
                if(comp && comp.indexOf(match.to[0].id) === -1) {

                    //console.log('SAFE TO REMOVE EDGE: ('+match.from.info+') -----> ('+match.to[0].info+')');
                    for(var di=0; di<match.from.domain.length; di++) {
                        var domainNode = match.from.domain[di];
                        if(domainNode.id === match.id) 
                            deadEnd.push(tt);
                    }

                    return { variable: match.from, edges: deadEnd };
                } else return undefined;
            }).compact().value();

        inferences.push.apply(inferences, inf);

        return inferences.length > 0; // modified?
    }

//#############################################
////////// ALT. CONSISTENCY ALGORITHMS  //////
//#############################################


function ac3(csp, inferences) {
    //console.log("AC3 running...");
    var Q = []; 
    initializeQueue(csp.cMap[UNARY], Q);
    initializeQueue(csp.cMap[BINARY], Q);
    initializeQueue(csp.cMap[NARY], Q);
    
    while(Q.length > 0) {
        var arc = Q.shift();
        if(typeof arc === undefined) continue; // FIXME avoid pushing undefined arcs

        switch(parseInt(arc[CNST].type)){
            case UNARY:
            case BINARY:
                if(csp.revise(arc[CNST], inferences, arc[1])) {
                    if(arc[1][0].domain.length === 0) 
                        return FAILURE; 
                    queueAffectedNodes(Q, arc[1]);
                }
                break;
            case NARY:
                if(arc[CNST].global) {
                    var reviseParams = [];
                    var result = arc[CNST].check(arc[1], reviseParams);
                    if(result) {
                        reviseParams.push(inferences); // will pass them into custom global
                        var modified = arc[CNST].global.apply(null, reviseParams); // logic has a global override
                        if(modified) {
                            //console.log('Domains modified by cusom revision function.');
                            for(var v in arc[1]) {
                                if(arc[1][v].domain.length === 0)
                                    return FAILURE;
                                else queueAffectedNodes(Q, (_.without(arc[1], v).unshift(v)));
                            } 
                        } 
                    } else {
                        //console.log('FAILURE returned from nary constraint');
                        return FAILURE; 
                    }
                } else console.warn('Not yet implemented');
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
    this.stats = { depth: 0, max: 0, inf: 0, backtracks: 0, time: null};
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
        cMap[cnst.type].push(cnst);
    });


    // before building, we want all variables in vMap, all edges (constraints+assignments)
    this.buildConstraintGraph();

    // TODO sort variables by inspecting constraints
}


csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.vMap, function(node){assignment[node.info]=node});

    var start = Date.now();
    var solution = this.backTrack(assignment);
    this.stats.time = (Date.now() - start);

    if(solution !== FAILURE) {
        console.log("\n\nSolved in "+
                (this.stats.time < 1000 ? this.stats.time+" ms" : this.stats.time/1000+" seconds") + "!" +
                "\ndepth: "+this.stats.depth +
                "\nmax depth: "+this.stats.max +
                "\ninferences: "+this.stats.inf +
                "\nbacktracks: "+this.stats.backtracks+"\n\n\n");
        printSolution(solution);
    } else console.log("Failed to find a solution");
}

function printSolution(sol) {
    var per=0,pet=1,col=2,drnk=3,cand=4;

    var houses = new Array(5);
    houses[per] = new Array(5);
    houses[pet] = new Array(5);
    houses[col] = new Array(5);
    houses[drnk] = new Array(5);
    houses[cand] = new Array(5);

    for(var i=0; i<5; i++) {
        for(var v in sol) {
            for(var d in sol[v].domain) {
                if(!sol[v].domain[d].to)
                    continue;
                else {
                    var varName = sol[v].info;
                    var houseNum = sol[v].domain[d].to[0].info-1;
                    if(people.indexOf(varName) !== -1)
                        houses[houseNum][per] = varName;
                    else if(pets.indexOf(sol[v].info) !== -1)
                        houses[houseNum][pet] = varName;
                    else if(colors.indexOf(sol[v].info) !== -1)
                        houses[houseNum][col] = varName;
                    else if(drinks.indexOf(sol[v].info) !== -1)
                        houses[houseNum][drnk] = varName;
                    else if(candies.indexOf(sol[v].info) !== -1)
                        houses[houseNum][cand] = varName;
                }
            }
        }
    }

    function pretty(slot) {
        return slot + (k==4 ? '\n' : 
            ((slot.length < 8) ? '\t\t' : '\t'));
    }

    var hstr = ''
    for(var i=0; i<5; i++)  {
        for(var k=0; k<5; k++) {
            debugger;
            hstr += pretty(houses[k][i]);
           // hstr += houses[per][i] + sp + houses[pet][i] + sp + houses[col][i] + sp +  houses[drnk][i] + sp + houses[cand][i] + '\n'; 
        }
    }
    console.log(hstr);
}

// I believe this can easily be generalized to n-ary
// However, it would be very inefficient for some constraints.
// For this reason, I'm including a 'global' function in the definition
// of a constraint which will allow me to override this logic
csp.prototype.revise = function(cnst, inferences, params) {
    var pivotVar = params[0];
    var modified = false;
    // if no value for v2 exists in C(v1,v2), remove v1 from domaim
    _.each(pivotVar.domain, function(assnEdge){
        var found=false;
        var pivotVal = assnEdge.to[0];
        var targetVar = parseInt(cnst.type) === UNARY ? pivotVar : params[1]; // UGLY unary case
        for(var t=0; t<targetVar.domain.length; t++) { 
            var targetVal = targetVar.domain[t].to[0]; // domain node
            if(cnst.check(pivotVal, targetVal)) { 
                found = true;
                break;
            }
        }
        if(!found) {
            pivotVar.domain = _.without(pivotVar.domain, assnEdge);
            inferences.push({variable: pivotVar, edges: [assnEdge]});
            modified = true;
        }
    });
    return modified;
}

csp.prototype.revert = function(inferences) {
    this.stats.backtracks++;
    //console.log('REVERTING');
    if(!inferences) return;
    while(inferences.length > 0) {
        var inf = inferences.pop();
        _.each(inf.edges, function(edge){inf.variable.domain.push(edge);});
    }
}

// TODO use array, not map, and sort on the array during csp construction
csp.prototype.getMostConstrainedVar = function() {
    var most; // most so far
    for(var name in this.vMap) {
        var variable = this.vMap[name];

        if(!variable instanceof Vertex || variable.domain.length < 2)  // Debugging only, TODO delete
            continue;

        if(!most || 
                variable.constraints.length > most.constraints.length) 
            most = variable;
    }
    return most || null;
}

// In my hypergraph formulation, inferences are simply edges in the
// bipartite variable->value representation
// A "{var = value}" assignment can be represented by its inverse,
// the set of edges removed in order to specify the assignemnt.
// In this way, state reparation is very straightforward.
csp.prototype.backTrack = function(assignment) {
    this.stats.depth++;
    if(this.stats.depth > this.stats.max)
        this.stats.max = this.stats.depth;

    var considered = this.getMostConstrainedVar();

    if(considered === null) 
        return assignment;

    var inferences;
    for(var vn in this.domain) {
        var valNode = this.domain[vn];
        //console.log('testing '+considered.info+' = '+valNode.info);
        if(hasDomainValue(considered, valNode.info)) {
            // verify boundary conditions
            inferences = forceSelection(considered, valNode);
            var ret = this.infer(assignment, inferences);
            if(ret !== FAILURE) { 
                var recur = this.backTrack(assignment);
                if(recur !== FAILURE)
                    return recur;
            } else {
                this.stats.backtracks++;
                this.stats.depth = 0;
            }
        }
        // completely revert
        this.revert(inferences); // adds the edges back into the graph
    }
    return FAILURE;
}

csp.prototype.infer = function(assignment, inferences) {
    this.stats.inf++;
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
    // consider adding constraint/assignment arrays

    _.each(this.vMap, function(varNode){
        vertices.push(varNode); // add to graph collection
        _.each(self.domain, function(valNode){
            var ass = new Assignment(varNode, valNode);
            //ass.capacity = Infinity;
            varNode.addAssignment(ass);
        });
    });

    for(var type in this.cMap){
        switch(parseInt(type)) {
            case UNARY:
                break;
            case BINARY:
                _.each(this.cMap[type], function(cc){
                    for(var i=0; i<cc.scope.length; i++) {
                        //if(!cc.scope[i]) continue; - FIXED TODO remove if verified
                        var vertex = self.vMap[cc.scope[i].info]; // get from the collection
                        cc.to.push(vertex);
                        var others = _.without(cc.scope, vertex.info);
                        _.each(others, function(affected){
                            vertex.addConstraint(cc);
                        });
                    }
                });
                break;
            case NARY:
                break;
            default:
                break;
        }
    }

    var graph = new ConstraintGraph(vertices);
}


// If function is passed, it will be a global revision function.
// The revision argument will receive the extra parameter to check
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
    [ ["milk"], VALUE, [3]],
    [ people, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ pets, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ colors, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ drinks, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ candies, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ]
];

var problem = new csp(variables, domain, constraints);
problem.solve();
