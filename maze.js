/* 
 * maze.js
 * By Noor AlHiraki
 *
 */



/*
 * Javascript Array type prototype.
 * This function is used to randomize an array.
 */
Array.prototype.shuffle = function()
{
  for (var i = 0; i < this.length; i++)
  {
    var j = Math.floor(Math.random() * (i + 1));
    var t = this[j];
    this[j] = this[i];
    this[i] = t;
  }
  return this;
}



/*
 * AI Class.
 * Contains implementations of several AI algorithms.
 */
AI = new function()
{
  this.execTime = 0;
  this.expanded = 0;
  
  /*
   * State class.
   */
  this.State = function()
  {
    this.tried = false;
  }
  
  /*
   * Node class to use in Tree/Graph Search algorithms.
   */
  var Node = function(state)
  {
    this.state = state;
    this.action = null;
    this.parent = null;
    this.pathcost = 1;
    this.depth = 0;
  }
  
  /*
   * Defining the (action, result) structure to use as
   * the successor's function output.
   */
  this.ActionResult = function(action, result)
  {
    this.action = action;
    this.result = result;
  }
  
  /*
   * Expanding nodes function.
   */
  var expand = function(node)
  {
    var successors = new Array();
    var actres = problem.successorFn(node.state);
    for (var i = 0; i < actres.length; i++)
    {
      var n = new Node();
      n.state = actres[i].result;
      n.action = actres[i].action;
      n.parent = node;
      n.pathcost = node.pathcost + 1;
      n.depth = node.depth + 1;
      successors.push(n);
    }
    return successors;
  }
  
  /*
   * Solution function.
   */
  var solution = function(node)
  {
    var solution = new Array();
    while (node.depth > 0)
    {
      solution.push(node.action);
      node = node.parent;
    }
    return solution.reverse();
  }
  
  /*
   * Breadth-First Graph Search algorithm implementation.
   */
  this.bfs = function(problem, fringe)
  {
    var initTime = new Date();
    this.expanded = 0;
    for (var i = 0; i < problem.states.length; i++) problem.states[i].tried = false;
    fringe.push(new Node(problem.initState));
    while (fringe.length != 0)
    {
      var node = fringe.shift();
      if (node.state == problem.goalState)
      {
        this.execTime = new Date() - initTime;
        return problem.displaySolution(solution(node));
      }
      if (!node.state.tried)
      {
        node.state.tried = true;
        var successors = expand(node);
        this.expanded++;
        for (var i = 0; i < successors.length; i++) fringe.push(successors[i]);
      }
    }
    return false;
  }
  
  /*
   * Depth-First Graph Search algorithm implementation.
   */
  this.dfs = function(problem, fringe)
  {
    var initTime = new Date();
    this.expanded = 0;
    for (var i = 0; i < problem.states.length; i++) problem.states[i].tried = false;
    fringe.push(new Node(problem.initState));
    while (fringe.length != 0)
    {
      var node = fringe.pop();
      if (node.state == problem.goalState)
      {
        this.execTime = new Date() - initTime;
        return problem.displaySolution(solution(node));
      }
      if (!node.state.tried)
      {
        node.state.tried = true;
        var successors = expand(node);
        this.expanded++;
        for (var i = 0; i < successors.length; i++) fringe.push(successors[i]);
      }
    }
    return false;
  }
  
  /*
   * Greedy Best-First Graph Search algorithm implementation.
   */
  this.gbfs = function(problem, fringe)
  {
    var initTime = new Date();
    this.expanded = 0;
    for (var i = 0; i < problem.states.length; i++) problem.states[i].tried = false;
    fringe.push(new Node(problem.initState));
    while (fringe.length != 0)
    {
      var node = fringe.pop();
      if (node.state == problem.goalState)
      {
        this.execTime = new Date() - initTime;
        return problem.displaySolution(solution(node));
      }
      if (!node.state.tried)
      {
        node.state.tried = true;
        var successors = expand(node);
        this.expanded++;
        for (var i = 0; i < successors.length; i++) fringe.push(successors[i]);
        priority = function(n1, n2) {return problem.distanceFromGoal(n2.state) - problem.distanceFromGoal(n1.state);}
        fringe.sort(priority);
      }
    }
    return false;
  }
}



/*
 * Maze Class, represents the problem.
 */
Maze = function(N, M, el, initX, initY, goalX, goalY, backColor, wallColor, cellSize, pathColor, failColor)
{
  this.N = N;
  this.M = M;
  this.el = document.getElementById(el);
  this.cellSize = cellSize + 'px';
  
  this.initX = (initX) ? initX : 0;
  this.initY = (initY) ? initY : 0;
  this.goalX = (goalX) ? goalX : this.N-1;
  this.goalY = (goalY) ? goalY : this.M-1;
  
  /*
   * Colors used when building maze.
   */
  this.backColor = backColor;
  this.wallColor = wallColor;
  
  /*
   * Colors used when solving maze.
   */
  this.pathColor = pathColor;
  this.failColor = failColor;
  
  /*
   * Defining a two-dimensional Grid array
   * JavaScript doesn't support multi-dimensional arrays!
   */
  this.grid = new Array(N);
  for (var i = 0; i < N; i++) this.grid[i] = new Array(M);
  
  /*
   * Cell class, serves as a state.
   */
  var Cell = AI.State.prototype;
  var Cell = function(x, y)
  {
    this.x = x;
    this.y = y;
    this.el = null;
    this.visited = false;
    this.N = true;
    this.S = true;
    this.E = true;
    this.W = true;
  }
  
  /*
   * Create the maze grid.
   */
  this.states = new Array();
  for (var y = 0; y < M; y++)
  {
    for (var x = 0; x < N; x++)
    {
      this.grid[x][y] = new Cell(x, y);
      this.states.push(this.grid[x][y]);
    }
  }
  
  /*
   * Setting the initial and goal states.
   */
  this.initState = this.grid[this.initX][this.initY];
  this.goalState = this.grid[this.goalX][this.goalY];
  
  /*
   * For a given current state and an action,
   * returns the next state.
   */
  this.nextState = function(currentState, action)
  {
    var cell = currentState;
    var x = cell.x;
    var y = cell.y;
    if (action == 'E' && x < this.N) return this.grid[x+1][y];
    if (action == 'S' && y < this.M) return this.grid[x][y+1];
    if (action == 'W' && x > 0) return this.grid[x-1][y];
    if (action == 'N' && y > 0) return this.grid[x][y-1];
    return 'error';
  }
  
  /*
   * Determines if a given cell is inside the maze.
   */
  this.contains = function(x, y)
  {
    return x >= 0
        && x < this.N
        && y >= 0
        && y < this.M;
  }
  
  /*
   * Represents the Successor Function for generating the maze.
   * Finds neighboring cells in the maze. Every cell
   * has at least two neighboring cells in the maze.
   */
  this.findNeighbors = function(cell)
  {
    var x = cell.x;
    var y = cell.y;
    var nbs = new Array();
    if (this.contains(x, y-1)) nbs.push(new AI.ActionResult('N', this.grid[x][y-1]));
    if (this.contains(x, y+1)) nbs.push(new AI.ActionResult('S', this.grid[x][y+1]));
    if (this.contains(x+1, y)) nbs.push(new AI.ActionResult('E', this.grid[x+1][y]));
    if (this.contains(x-1, y)) nbs.push(new AI.ActionResult('W', this.grid[x-1][y]));
    return nbs;
  }
  
  /*
   * The successor function for solving the maze.
   */
  this.successorFn = function(state)
  {
    var cell = state;
    var x = cell.x;
    var y = cell.y;
    var successors = new Array();
    if (!cell.N && this.contains(x, y-1)) successors.push(new AI.ActionResult('N', this.grid[x][y-1]));
    if (!cell.S && this.contains(x, y+1)) successors.push(new AI.ActionResult('S', this.grid[x][y+1]));
    if (!cell.E && this.contains(x+1, y)) successors.push(new AI.ActionResult('E', this.grid[x+1][y]));
    if (!cell.W && this.contains(x-1, y)) successors.push(new AI.ActionResult('W', this.grid[x-1][y]));
    return successors;
  }
    
  /*
   * The Euclidean distance between a cell and the goal.
   * Represenets a heuristic function.
   */
  this.distanceFromGoal = function(cell)
  {
    var xs = Math.pow((cell.x - this.goalState.x), 2);
    var ys = Math.pow((cell.y - this.goalState.y), 2);
    var d = Math.sqrt(xs + ys);
    return d;
  }
  
  /*
   * Given two adjacent cells, this removes their
   * common border.
   */
  this.removeWall = function(c1, c2)
  {
    if        (c1.x < c2.x) { c1.E = false; c2.W = false;
    } else if (c2.x < c1.x) { c2.E = false; c1.W = false;
    } else if (c1.y < c2.y) { c1.S = false; c2.N = false;
    } else if (c2.y < c1.y) { c2.S = false; c1.N = false;
    }
  }
  
  /*
   * Recursive DFS Algorithm for generating the Maze.
   */
  this.buildPath = function(cell)
  {
    cell.visited = true;
    var nbs = this.findNeighbors(cell);
    nbs.shuffle();
    
    for (var i = 0; i < nbs.length; i++)
    {
      var nb = nbs[i].result;
      if (!nb.visited)
      {
        this.removeWall(cell, nb);
        this.buildPath(nb);
      }
    }
  }
  
  /*
   * Clears child nodes from the current maze HTML element.
   */
  this.clearMaze = function()
  {
    while(this.el.firstChild) this.el.removeChild(this.el.firstChild);
  }
  
  /*
   * Renders the maze in HTML.
   */
  this.displayMaze = function(openColor, wallColor, cellSize)
  {
    this.clearMaze();
    this.el.style.width = this.N * (parseInt(cellSize) + 1) + 1 + 'px';
    for (var y = 0; y < this.M; y++)
    {
      for (var x = 0; x < this.N; x++)
      {
        var cell = this.grid[x][y];
        var el = document.createElement('DIV');
        cell.el = el;
        this.el.appendChild(el);
        
        var wall = '1px solid ' + wallColor;
        var open = '1px solid ' + openColor;
        el.style.borderRight  = cell.E ? wall : open;
        el.style.borderBottom = cell.S ? wall : open;
        if (x == 0) el.style.borderLeft = cell.W ? wall : open;
        if (y == 0) el.style.borderTop = cell.N ? wall : open;
        el.style.cssFloat = el.style.styleFloat = 'left';
        
        el.style.height = 
        el.style.width = 
        el.style.lineHeight = 
        el.style.fontSize = cellSize;
        el.style.textAlign = 'center';
        el.style.backgroundColor = openColor;
        el.style.color = wallColor;
        el.style.cursor = 'pointer';
        
        el.x = x; el.y = y;
        el.oncontextmenu = function(e) {return false;}
        el.onmousedown = function(e)
        {
          e = e || window.event;
          obj = (e.target)? e.target : e.srcElement;
          rightClick = (e.which == 3) || (e.button == 2);
          leftClick = (e.which == 1) || (e.button == 1);
          if (leftClick) setInitState(obj.x, obj.y);
          if (rightClick) setGoalState(obj.x, obj.y);
        }
      }
    }
    this.initState.el.innerHTML = '&bull;';
    this.goalState.el.innerHTML = '&times;';
  }
  
  /*
   * Clears all paths.
   */
  this.clearSolution = function()
  {
    document.getElementById('actions').innerHTML = "";
    document.getElementById('time').innerHTML = "";
    document.getElementById('expanded').innerHTML = "";
    for (var y = 0; y < this.M; y++)
    {
      for (var x = 0; x < this.N; x++)
      {
        this.grid[x][y].el.style.backgroundColor = '';
      }
    }
  }
  
  /*
   * Renders a path, using an array of actions as an input.
   */
  this.displaySolution = function(actions)
  {
	/*
     * Renders all tried cells that didn't lead to the goal.
     */
    for (var i = 0; i < this.states.length; i++)
    {
      if(this.states[i].tried) this.states[i].el.style.backgroundColor = this.failColor;
    }
    
    var state = this.initState;
    for (var i = 0; i < actions.length; i++)
    {
      state.el.style.backgroundColor = this.pathColor;
      document.getElementById('actions').innerHTML += actions[i] + " ";
      state = this.nextState(state, actions[i]);
    }
    document.getElementById('time').innerHTML = AI.execTime + ' milliseconds';
    document.getElementById('expanded').innerHTML = AI.expanded + ' nodes';
    state.el.style.backgroundColor = this.pathColor;
  }
  
  /*
   * Renders all tried cells that didn't lead to the goal.
   */
  this.displayTried = function()
  {
    for (var i = 0; i < this.states.length; i++)
    {
      if(this.states[i].tried) this.states[i].el.style.backgroundColor = this.failColor;
    }
  }
  
  /*
   * Finally; build the maze then display it and return the maze object.
   */
  this.buildPath(this.initState);
  this.displayMaze(this.backColor, this.wallColor, this.cellSize);
  return this;
}



/*
 * Global Functions
 */

function getSeleVal(id)
{
  return parseInt(document.getElementById(id).value);
}

function generateMaze()
{
  problem = new Maze(getSeleVal('mazeW'), getSeleVal('mazeH'), 'maze', 0, 0, getSeleVal('mazeW')-1, getSeleVal('mazeH')-1, 'white', 'black', getSeleVal('cellSize'), 'rgb(160,240,200)', 'rgb(150,220,255)');
  document.getElementById('init').value = problem.initX + ', ' + problem.initY;
  document.getElementById('goal').value = problem.goalX + ', ' + problem.goalY;
  problem.clearSolution();
}

function solve(problem, algorithm)
{
  var fringe = new Array();
  var start = problem.initState;
  if (algorithm == 'dfs') AI.dfs(problem, fringe);
  if (algorithm == 'bfs') AI.bfs(problem, fringe);
  if (algorithm == 'gbfs') AI.gbfs(problem, fringe);
}

setInitState = function(x, y)
{
  problem.initState.el.innerHTML = '';
  problem.goalState.el.innerHTML = '';
  problem.initState = problem.grid[x][y];
  document.getElementById('init').value = x + ', ' + y;
  problem.initState.el.innerHTML = '&bull;';
  problem.goalState.el.innerHTML = '&times;';
  problem.clearSolution();
}

setGoalState = function(x, y)
{
  problem.initState.el.innerHTML = '';
  problem.goalState.el.innerHTML = '';
  problem.goalState = problem.grid[x][y];
  document.getElementById('goal').value = x + ', ' + y;
  problem.initState.el.innerHTML = '&bull;';
  problem.goalState.el.innerHTML = '&times;';
  problem.clearSolution();
}