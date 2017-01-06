var app = require('http').createServer(onRequest);
var io = require('socket.io')(app);
var fs = require('fs');
var url = require('url');

process.on('uncaughtException', function(err) {
    console.log(err);
});

var ip_addr = process.env.IP   || process.env.OPENSHIFT_NODEJS_IP || '0.0.0.0';
var port    = process.env.PORT || process.env.OPENSHIFT_NODEJS_PORT || 8080;

var RED = "#ff7070",
	GREEN = "#7cdb69",
	WHITE = "#ffffff",
	BLUE = "#898dff",
	GLAY = "#c0c0c0",
	YELLOW = "#eeee00";
var board =	[[GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY]];
var vel = [[0,1],[-1,1],[-1,0],[-1,-1],[0,-1],[1,-1],[1,0],[1,1]];
var change_cells = [];
var points = {"#ff7070": 0, "#7cdb69": 0, "#ffffff": 0, "#898dff": 0, "#c0c0c0": 25, "#eeee00": 0};
var users=[];
var answer = [];
var memo="";
var white_board=[];
var pingTime=0;
var reqURLs = {
				"/": "index.html",
				"/index.html": "index.html",
				"/index2.html": "index2.html",
				"/master": "master.html",
				"/favicon.ico": "favicon.ico",
				"/sounds/maru.mp3": "sounds/maru.mp3",
				"/sounds/maru0.mp3": "sounds/maru0.mp3",
				"/sounds/maru1.mp3": "sounds/maru1.mp3",
				"/sounds/maru2.mp3": "sounds/maru2.mp3",
				"/sounds/maru3.mp3": "sounds/maru3.mp3",
				"/sounds/maru4.mp3": "sounds/maru4.mp3",
				"/sounds/batsu.mp3": "sounds/batsu.mp3",
				"/sounds/batsu25.mp3": "sounds/batsu25.mp3",
				"/sounds/think.mp3": "sounds/think.mp3",
				"/sounds/red.mp3": "sounds/red.mp3",
				"/sounds/green.mp3": "sounds/green.mp3",
				"/sounds/white.mp3": "sounds/white.mp3",
				"/sounds/blue.mp3": "sounds/blue.mp3",
				"/images/maru.png": "images/maru.png",
				"/images/batsu.png": "images/batsu.png",
				"/source": "source/index.html",
				"/source/": "source/index.html",
				"/source/index.html": "source/index.html",
				"/source/app.js": "app.js"
			};

//MT-----------------------------------
function MersenneTwister(seed) {
	if (arguments.length == 0)
		seed = new Date().getTime();

	this._mt = new Array(624);
	this.setSeed(seed);
}

MersenneTwister._mulUint32 = function(a, b) {
	var a1 = a >>> 16, a2 = a & 0xffff;
	var b1 = b >>> 16, b2 = b & 0xffff;
	return (((a1 * b2 + a2 * b1) << 16) + a2 * b2) >>> 0;
};

MersenneTwister._toNumber = function(x) {
	return (typeof x == "number" && !isNaN(x)) ? Math.ceil(x) : 0;
};

MersenneTwister.prototype.setSeed = function(seed) {
	var mt = this._mt;
	if (typeof seed == "number") {
		mt[0] = seed >>> 0;
		for (var i = 1; i < mt.length; i++) {
			var x = mt[i-1] ^ (mt[i-1] >>> 30);
			mt[i] = MersenneTwister._mulUint32(1812433253, x) + i;
		}
		this._index = mt.length;
	} else if (seed instanceof Array) {
		var i = 1, j = 0;
		this.setSeed(19650218);
		for (var k = Math.max(mt.length, seed.length); k > 0; k--) {
			var x = mt[i-1] ^ (mt[i-1] >>> 30);
			x = MersenneTwister._mulUint32(x, 1664525);
			mt[i] = (mt[i] ^ x) + (seed[j] >>> 0) + j;
			if (++i >= mt.length) {
				mt[0] = mt[mt.length-1];
				i = 1;
			}
			if (++j >= seed.length) {
				j = 0;
			}
		}
		for (var k = mt.length - 1; k > 0; k--) {
			var x = mt[i-1] ^ (mt[i-1] >>> 30);
			x = MersenneTwister._mulUint32(x, 1566083941);
			mt[i] = (mt[i] ^ x) - i;
			if (++i >= mt.length) {
				mt[0] = mt[mt.length-1];
				i = 1;
			}
		}
		mt[0] = 0x80000000;
	} else {
		throw new TypeError("MersenneTwister: illegal seed.");
	}
};

MersenneTwister.prototype._nextInt = function() {
	var mt = this._mt, value;

	if (this._index >= mt.length) {
		var k = 0, N = mt.length, M = 397;
		do {
			value = (mt[k] & 0x80000000) | (mt[k+1] & 0x7fffffff);
			mt[k] = mt[k+M] ^ (value >>> 1) ^ ((value & 1) ? 0x9908b0df : 0);
		} while (++k < N-M);
		do {
			value = (mt[k] & 0x80000000) | (mt[k+1] & 0x7fffffff);
			mt[k] = mt[k+M-N] ^ (value >>> 1) ^ ((value & 1) ? 0x9908b0df : 0);
		} while (++k < N-1);
		value = (mt[N-1] & 0x80000000) | (mt[0] & 0x7fffffff);
		mt[N-1] = mt[M-1] ^ (value >>> 1) ^ ((value & 1) ? 0x9908b0df : 0);
		this._index = 0;
	}

	value = mt[this._index++];
	value ^=  value >>> 11;
	value ^= (value <<   7) & 0x9d2c5680;
	value ^= (value <<  15) & 0xefc60000;
	value ^=  value >>> 18;
	return value >>> 0;
};

MersenneTwister.prototype.nextInt = function() {
	var min, sup;
	switch (arguments.length) {
	case 0:
		return this._nextInt();
	case 1:
		min = 0;
		sup = MersenneTwister._toNumber(arguments[0]);
		break;
	default:
		min = MersenneTwister._toNumber(arguments[0]);
		sup = MersenneTwister._toNumber(arguments[1]) - min;
		break;
	}

	if (!(0 < sup && sup < 0x100000000))
		return this._nextInt() + min;
	if ((sup & (~sup + 1)) == sup)
		return ((sup - 1) & this._nextInt()) + min;

	var value;
	do {
		value = this._nextInt();
	} while (sup > 4294967296 - (value - (value %= sup)));
	return value + min;
};

MersenneTwister.prototype.next = function() {
	var a = this._nextInt() >>> 5, b = this._nextInt() >>> 6;
	return (a * 0x4000000 + b) / 0x20000000000000;
};

var mt = new MersenneTwister();
//MT-----------------------------------

function onRequest(req, res) {
	var pathname = url.parse(req.url).pathname;
	if(pathname in reqURLs){
		fs.readFile(reqURLs[pathname], function (err, data) {
		if (err) {	//ファイル読み込みエラー処理
			res.writeHead(700);
			return res.end('Error loading ' + pathname);
		}
		res.writeHead(200);
		res.end(data);
	});
	}else{	//その他のリクエストにはindex.htmlを返す
		fs.readFile("index.html", function (err, data) {
			if (err) {
				res.writeHead(700);
				return res.end('Error loading ' + pathname);
			}
			res.writeHead(200);
			res.end(data);
		});
	}
}

function othello(data,r,c,vel){
	y=vel[0];
	x=vel[1];
	for(i=r+y, j=c+x; i<5 && i>=0 && j<5 && j>=0; i=i+y, j=j+x){
		bgcolor = board[i][j];
		if(bgcolor == GLAY){
			return;
		}else if(bgcolor == data){
			for(m=r+y, n=c+x; m!=i || n!=j; m=m+y, n=n+x){
				change_cells.push([m,n]);
			}
			return;
		}
	}
}

function change_colors(change_cells,data){
	if(change_cells.length == 0) return;
	index = change_cells.shift();
	if(board[index[0]][index[1]] != data){
		--points[board[index[0]][index[1]]];
		board[index[0]][index[1]] = data;
		++points[board[index[0]][index[1]]];
		if(data == RED) io.emit("sound","red");
		else if(data == GREEN) io.emit("sound","green");
		else if(data == WHITE) io.emit("sound","white");
		else if(data == BLUE) io.emit("sound","blue");
		io.emit("update", [board, points]);
	}
	setTimeout(function(){
		change_colors(change_cells,data);
	},600);
}

function users_emit(){
	users=[];
	pingTime=+new Date();
	io.emit("ping",pingTime); //新規接続時に生存確認
	setTimeout(function(){
		users.sort(
			function(a, b){
				if(a["user"] < b["user"]) return -1;
				return 1;
			});
		io.emit("users", users);
	},1000);
}

io.on('connection', function (soc) {	//クライアント接続時
	console.log('new connection.');

	soc.on('on connect', function (data){	//これ以降は第一引数に当てはまるイベント受信時に処理
		console.log('keeping connection.');
		if(data["time"]==pingTime){
			users.push(data);
		}
	});

	soc.on("sound", function(data){
		io.emit("sound",data); //master含めて全ユーザーにメッセージsoundを送信
	});

	soc.on("change", function(data){
		--points[board[data[0]][data[1]]];
		board[data[0]][data[1]]=data[2];
		++points[board[data[0]][data[1]]];
		if(data[2] == RED) io.emit("sound","red");
		else if(data[2] == GREEN) io.emit("sound","green");
		else if(data[2] == WHITE) io.emit("sound","white");
		else if(data[2] == BLUE) io.emit("sound","blue");
		io.emit("update", [board, points]);
		if(data[2] == GLAY || data[2] == YELLOW) return;
		for(var i in vel){
			othello(data[2],data[0],data[1],vel[i]);
		}
		setTimeout(function(){
			change_colors(change_cells,data[2]);
		},600);
		var glay_num = 0;
		for(var i = 0; i < 5; i++){
			for(var j = 0; j < 5; j++){
				if(board[i][j] == GLAY) glay_num++;
			}
		}
		if(glay_num == 5){
			io.emit("attack_chance");
		}else{
			io.emit("not_attack_chance");
		}
	});

	soc.on("p", function(data){
		for(var i = 0; i < answer.length; i++){
			if(answer[i][0]["player"] == data["player"]){
				return;
			}
		}
		answer.push([data,+new Date()]);
		io.emit("p", answer);
	});

	soc.on("answer_clear", function(){
		answer = [];
		io.emit("answer_clear");
	});

	soc.on("reset_table", function(){
		board =	[[GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY],
			 [GLAY,GLAY,GLAY,GLAY,GLAY]];
		points = {"#ff7070": 0, "#7cdb69": 0, "#ffffff": 0, "#898dff": 0, "#c0c0c0": 25, "#eeee00": 0};
		io.emit("update", [board, points]);
		io.emit("not_attack_chance");
	});

	soc.on("disconnect", function(data){	//切断時
		users_emit();
	});

	soc.on("change_info", function(){	//情報更新時
		users_emit();
	});

	soc.emit("init");
	users_emit();
	soc.emit("update", [board, points]);	//ボードと点数情報を新規クライアントに送信
	soc.emit("memo", memo);

	if(answer.length > 0){
		soc.emit("p", answer);
	}

	soc.on("chat", function(data){
		io.emit("chat", data);
	});

	soc.on("memo", function(data){
		memo=data;
		io.emit("memo", data);
	});

	soc.on("white_board", function(data){
		var isNewUser = true;
		for(var i in white_board){
			if(white_board[i]["user"] == data["user"] && white_board[i]["color"] == data["color"]){
				white_board[i]["text"] = data["text"];
				isNewUser = false;
				break;
			}
		}
		if(isNewUser){
			white_board.push(data);
		}
		for(var i in white_board){
			if(white_board[i]["text"] == ""){
				white_board.splice(i,1);
			}else{
				var isResistered = false;
				for(var j in users){
					if(users[j]["user"] == white_board[i]["user"] && users[j]["color"] == white_board[i]["color"]){
						isResistered = true;
						break;
					}
				}
				if(!isResistered){
					white_board.splice(i,1);
				}
			}
		}
		white_board.sort();
		io.emit("white_board", white_board);
	});

	soc.on("white_board_open", function(){
		io.emit("white_board_open", white_board);
	});

	soc.on("dice", function(data){
		io.emit("dice_val",[mt.nextInt()%(data[1]-data[0]+1)+data[0]*1]);
	});
	
	var glay_num = 0;
	for(var i = 0; i < 5; i++){
		for(var j = 0; j < 5; j++){
			if(board[i][j] == GLAY) glay_num++;
		}
	}
	if(glay_num == 5){
		io.emit("attack_chance");
	}else{
		io.emit("not_attack_chance");
	}
});

app.listen(port, ip_addr, function(){
	console.log('Server Working!');
});

console.log("Server is running.");
