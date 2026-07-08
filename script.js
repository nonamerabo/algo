/* ================================================================
   Algorithm Research Lab - script.js
   ----------------------------------------------------------------
   【クラス構成（保守性向上のため責務ごとに分離しています）】
     MazeGenerator   : 迷路の自動生成・経路探索（データ構造の管理）
     PlayerController: プレイヤーの位置・移動・探索ログの記録
     Analyzer        : 探索ログからDFS/BFS/線形探索らしさを診断（ルールベース）
     StorageManager  : 診断結果の保存・集計（今はlocalStorage／将来Firebase等に差し替え可能）
     QRManager       : 診断カードURLの組み立て・QRコード生成/表示
     UIManager       : 画面切り替え・HUD更新・演出などDOM操作全般
     ResultRenderer  : 診断結果画面／統計ページの描画
     GameManager     : 上記すべてを繋いでゲーム全体の流れを制御する司令塔

   なお SimpleQR（QRコードの符号化エンジン本体）と Renderer（キャンバス
   描画の共通関数集）は、上記クラスから利用される「低レベルの道具箱」
   として独立させています。
================================================================ */

"use strict";

/* ================================================================
   共通ユーティリティ
================================================================ */
function randInt(max) {
  return Math.floor(Math.random() * max);
}
function pickRandom(arr) {
  return arr[randInt(arr.length)];
}
/** 4〜6桁のランダムな被験者IDを生成する（演出用） */
function generateSubjectId() {
  const digits = 4 + randInt(3);
  let id = "";
  for (let i = 0; i < digits; i++) id += randInt(10);
  return id;
}
/** 統計保存用のユニークID（時刻＋乱数の組み合わせで衝突をほぼ回避しつつ、QR用に短く保つ） */
function generateRecordId() {
  return Date.now().toString(36).slice(-6) + Math.random().toString(36).slice(2, 6);
}
function formatTime(totalSeconds) {
  const s = Math.max(0, Math.round(totalSeconds));
  const m = Math.floor(s / 60).toString().padStart(2, "0");
  const ss = Math.floor(s % 60).toString().padStart(2, "0");
  return `${m}:${ss}`;
}
function cellKey(c, r) {
  return `${c},${r}`;
}


/* ================================================================
   MazeGenerator
   ----------------------------------------------------------------
   再帰的バックトラッカー法で、全マスが1本の通路網でつながった
   「木構造の迷路」を生成する。木構造なので寄り道は必ず行き止まりに
   なり、プレイヤーの探索傾向を測定しやすい。
================================================================ */
class MazeGenerator {
  constructor(cols, rows) {
    this.cols = cols;
    this.rows = rows;
    this.cells = [];
    for (let i = 0; i < cols * rows; i++) {
      this.cells.push({ N: true, E: true, S: true, W: true, visited: false });
    }
    this._generate();
    this.start = { c: 0, r: 0 };
    this.goal = this._findFarthestCell(this.start);
    this.treasure = this._findTreasureCell();
  }

  idx(c, r) { return r * this.cols + c; }
  cellAt(c, r) { return this.cells[this.idx(c, r)]; }
  inBounds(c, r) { return c >= 0 && c < this.cols && r >= 0 && r < this.rows; }

  _generate() {
    const DIRS = [
      { d: "N", dc: 0, dr: -1, o: "S" },
      { d: "E", dc: 1, dr: 0, o: "W" },
      { d: "S", dc: 0, dr: 1, o: "N" },
      { d: "W", dc: -1, dr: 0, o: "E" },
    ];
    const stack = [{ c: 0, r: 0 }];
    this.cellAt(0, 0).visited = true;

    while (stack.length > 0) {
      const cur = stack[stack.length - 1];
      const candidates = [];
      for (const dir of DIRS) {
        const nc = cur.c + dir.dc;
        const nr = cur.r + dir.dr;
        if (this.inBounds(nc, nr) && !this.cellAt(nc, nr).visited) {
          candidates.push({ ...dir, nc, nr });
        }
      }
      if (candidates.length > 0) {
        const chosen = pickRandom(candidates);
        this.cellAt(cur.c, cur.r)[chosen.d] = false;
        this.cellAt(chosen.nc, chosen.nr)[chosen.o] = false;
        this.cellAt(chosen.nc, chosen.nr).visited = true;
        stack.push({ c: chosen.nc, r: chosen.nr });
      } else {
        stack.pop();
      }
    }
  }

  neighborsOf(c, r) {
    const cell = this.cellAt(c, r);
    const result = [];
    if (!cell.N && this.inBounds(c, r - 1)) result.push({ c, r: r - 1, dir: "N" });
    if (!cell.E && this.inBounds(c + 1, r)) result.push({ c: c + 1, r, dir: "E" });
    if (!cell.S && this.inBounds(c, r + 1)) result.push({ c, r: r + 1, dir: "S" });
    if (!cell.W && this.inBounds(c - 1, r)) result.push({ c: c - 1, r, dir: "W" });
    return result;
  }

  isDeadEnd(c, r) {
    return this.neighborsOf(c, r).length === 1;
  }

  _findFarthestCell(from) {
    const dist = this._bfsDistances(from);
    let farthest = from;
    let maxDist = -1;
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const d = dist[this.idx(c, r)];
        if (d > maxDist) { maxDist = d; farthest = { c, r }; }
      }
    }
    return farthest;
  }

  _findTreasureCell() {
    const mainPath = this.shortestPath(this.start, this.goal).map((p) => cellKey(p.c, p.r));
    const mainPathSet = new Set(mainPath);
    const deadEnds = [];
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (c === this.start.c && r === this.start.r) continue;
        if (this.isDeadEnd(c, r) && !mainPathSet.has(cellKey(c, r))) {
          deadEnds.push({ c, r });
        }
      }
    }
    if (deadEnds.length === 0) {
      return mainPath.length > 1 ? { c: this.goal.c, r: this.goal.r } : this.start;
    }
    const distFromStart = this._bfsDistances(this.start);
    deadEnds.sort((a, b) => distFromStart[this.idx(b.c, b.r)] - distFromStart[this.idx(a.c, a.r)]);
    return deadEnds[Math.floor(deadEnds.length / 3)] || deadEnds[0];
  }

  _bfsDistances(from) {
    const dist = new Array(this.cols * this.rows).fill(-1);
    dist[this.idx(from.c, from.r)] = 0;
    const queue = [from];
    let head = 0;
    while (head < queue.length) {
      const cur = queue[head++];
      const curDist = dist[this.idx(cur.c, cur.r)];
      for (const n of this.neighborsOf(cur.c, cur.r)) {
        if (dist[this.idx(n.c, n.r)] === -1) {
          dist[this.idx(n.c, n.r)] = curDist + 1;
          queue.push(n);
        }
      }
    }
    return dist;
  }

  shortestPath(from, to) {
    const prev = new Map();
    const visited = new Set([cellKey(from.c, from.r)]);
    const queue = [from];
    let head = 0;
    while (head < queue.length) {
      const cur = queue[head++];
      if (cur.c === to.c && cur.r === to.r) break;
      for (const n of this.neighborsOf(cur.c, cur.r)) {
        const key = cellKey(n.c, n.r);
        if (!visited.has(key)) {
          visited.add(key);
          prev.set(key, cur);
          queue.push(n);
        }
      }
    }
    const path = [];
    let cur = to;
    path.push(cur);
    while (!(cur.c === from.c && cur.r === from.r)) {
      const key = cellKey(cur.c, cur.r);
      cur = prev.get(key);
      if (!cur) break;
      path.push(cur);
    }
    return path.reverse();
  }

  /** DFS（優先順 N,E,S,W固定）で目的地に着くまでの全移動手順をシミュレートする */
  simulateDFSPath(from, to) {
    const visited = new Set([cellKey(from.c, from.r)]);
    const path = [from];
    const self = this;
    function dfs(node) {
      if (node.c === to.c && node.r === to.r) return true;
      const neighbors = self.neighborsOf(node.c, node.r);
      for (const n of neighbors) {
        const key = cellKey(n.c, n.r);
        if (!visited.has(key)) {
          visited.add(key);
          path.push(n);
          if (dfs(n)) return true;
          path.push(node);
        }
      }
      return false;
    }
    dfs(from);
    return path;
  }

  totalCells() { return this.cols * this.rows; }

  totalDeadEnds() {
    let count = 0;
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if ((c !== this.start.c || r !== this.start.r) && this.isDeadEnd(c, r)) count++;
      }
    }
    return count;
  }
}


/* ================================================================
   PlayerController
   ----------------------------------------------------------------
   プレイヤーの位置管理・移動処理に加えて、探索ログ（歩数・行き止まり
   訪問回数・分岐での選択傾向など）の記録も担当する。
   「プレイヤーを操作すること」と「操作の履歴を記録すること」は
   一体の責務として、このクラスにまとめている。
================================================================ */
class PlayerController {
  constructor(maze) {
    this.maze = maze;
    this.c = maze.start.c;
    this.r = maze.start.r;
    this.drawC = this.c; // 画面上の実際の描画位置（アニメーション用に少し遅れて追従する）
    this.drawR = this.r;
    this.moving = false;

    this.path = [{ c: this.c, r: this.r }];
    this.visitCounts = new Map([[cellKey(this.c, this.r), 1]]);
    this.revisitCount = 0;
    this.deadEndVisits = 0;
    this.branchDecisions = [];
    this.treasureCollected = false;
    this.treasureStepIndex = null;
    this.startTime = null;
    this.endTime = null;
  }

  startClock() { this.startTime = performance.now(); }
  stopClock() { this.endTime = performance.now(); }

  /**
   * 方向キー入力を受けて移動を試みる。
   * @param {"up"|"down"|"left"|"right"} dir
   * @returns {{moved:boolean, reachedGoal:boolean, treasureJustCollected:boolean}}
   */
  tryMove(dir) {
    if (this.moving) return { moved: false, reachedGoal: false, treasureJustCollected: false };
    const DIR_MAP = {
      up: { key: "N", dc: 0, dr: -1 },
      down: { key: "S", dc: 0, dr: 1 },
      left: { key: "W", dc: -1, dr: 0 },
      right: { key: "E", dc: 1, dr: 0 },
    };
    const d = DIR_MAP[dir];
    if (!d) return { moved: false, reachedGoal: false, treasureJustCollected: false };

    const cell = this.maze.cellAt(this.c, this.r);
    if (cell[d.key]) return { moved: false, reachedGoal: false, treasureJustCollected: false }; // 壁がある

    const from = { c: this.c, r: this.r };
    const to = { c: this.c + d.dc, r: this.r + d.dr };
    this._recordMove(from, to);

    this.c = to.c;
    this.r = to.r;
    this.moving = true;

    const treasureJustCollected =
      this.treasureCollected && this.treasureStepIndex === this.path.length - 1;
    const reachedGoal = to.c === this.maze.goal.c && to.r === this.maze.goal.r;

    return { moved: true, reachedGoal, treasureJustCollected };
  }

  /** 移動の記録（歩数・行き止まり・分岐選択傾向など） */
  _recordMove(fromCell, toCell) {
    const toKey = cellKey(toCell.c, toCell.r);
    const wasVisited = this.visitCounts.has(toKey);

    const branchOptions = this.maze.neighborsOf(fromCell.c, fromCell.r);
    if (branchOptions.length >= 3) {
      const chosenUnvisited = !wasVisited;
      const firstOption = branchOptions[0];
      const chosenFirstOption = firstOption.c === toCell.c && firstOption.r === toCell.r;
      this.branchDecisions.push({ chosenUnvisited, chosenFirstOption });
    }

    if (wasVisited) {
      this.revisitCount++;
      this.visitCounts.set(toKey, this.visitCounts.get(toKey) + 1);
    } else {
      this.visitCounts.set(toKey, 1);
    }

    if (this.maze.isDeadEnd(toCell.c, toCell.r) &&
        !(toCell.c === this.maze.start.c && toCell.r === this.maze.start.r)) {
      this.deadEndVisits++;
    }

    this.path.push({ ...toCell });

    if (!this.treasureCollected &&
        toCell.c === this.maze.treasure.c && toCell.r === this.maze.treasure.r) {
      this.treasureCollected = true;
      this.treasureStepIndex = this.path.length - 1;
    }
  }

  /** 毎フレーム呼び出し、見た目の座標を目的地へ滑らかに近づける */
  updateAnimation(lerpSpeed = 0.28) {
    const dc = this.c - this.drawC;
    const dr = this.r - this.drawR;
    if (Math.abs(dc) > 0.01 || Math.abs(dr) > 0.01) {
      this.drawC += dc * lerpSpeed;
      this.drawR += dr * lerpSpeed;
    } else {
      this.drawC = this.c;
      this.drawR = this.r;
      this.moving = false;
    }
  }

  get totalSteps() { return this.path.length - 1; }
  get elapsedSeconds() {
    const end = this.endTime || performance.now();
    return (end - this.startTime) / 1000;
  }
  get uniqueVisitedCount() { return this.visitCounts.size; }
  get explorationRate() { return (this.uniqueVisitedCount / this.maze.totalCells()) * 100; }

  get unexploredPriorityRatio() {
    if (this.branchDecisions.length === 0) return 0.5;
    const count = this.branchDecisions.filter((b) => b.chosenUnvisited).length;
    return count / this.branchDecisions.length;
  }
  get systematicChoiceRatio() {
    if (this.branchDecisions.length === 0) return 0.5;
    const count = this.branchDecisions.filter((b) => b.chosenFirstOption).length;
    return count / this.branchDecisions.length;
  }
  get deadEndRatio() {
    const total = this.maze.totalDeadEnds();
    if (total === 0) return 0;
    return Math.min(1, this.deadEndVisits / total);
  }
  get idealSteps() {
    const toTreasure = this.maze.shortestPath(this.maze.start, this.maze.treasure).length - 1;
    const toGoal = this.maze.shortestPath(this.maze.treasure, this.maze.goal).length - 1;
    return toTreasure + toGoal;
  }
  get stepDiff() { return this.totalSteps - this.idealSteps; }
}


/* ================================================================
   Analyzer
   ----------------------------------------------------------------
   生成AIは一切使用していません。PlayerControllerが記録した行動
   データから、複数のルール（重み付けスコア）でDFS/BFS/線形探索の
   「らしさ」を算出する、完全にルールベースの判定です。
================================================================ */
const Analyzer = {
  // 称号・コメントは「typeコード＋バリエーション番号」で管理する。
  // QRコード経由で診断カードを表示する際も、同じ番号から同じ文章を
  // 再現できるようにするための設計（URLのペイロードを軽量化するため）。
  TITLE_POOL: {
    D: ["探究者", "冒険家", "未知への挑戦者"],
    B: ["最短マスター", "効率の探検家", "先読みの達人"],
    L: ["慎重派", "丁寧な観察者", "一歩ずつの職人"],
    X: ["アルゴリズム博士"],
  },
  COMMENT_POOL: {
    D: [
      "未知の道を最後まで探索する傾向があります。",
      "一度決めた道を最後まで調べるタイプです。",
      "行き止まりを恐れず、奥へ奥へと進んでいく探検家気質です。",
    ],
    B: [
      "周囲を広く確認してから進む傾向があります。",
      "効率良く最短経路を探すことが得意です。",
      "無駄のないルート選びで、ゴールまで最短距離を描き出します。",
    ],
    L: [
      "一つずつ丁寧に確認する慎重派です。",
      "順序立てて、着実に道を調べていくタイプです。",
      "焦らず一手ずつ、確実に選択肢をつぶしていく職人肌です。",
    ],
    X: ["DFS・BFS・線形探索、すべての思考を兼ね備えた稀有なタイプです。"],
  },

  /** @param {PlayerController} player */
  analyze(player) {
    const idealSteps = Math.max(1, player.idealSteps);
    const diffRatio = Math.max(0, player.stepDiff) / idealSteps;
    const deadEndRatio = player.deadEndRatio;
    const unexploredRatio = player.unexploredPriorityRatio;
    const systematicRatio = player.systematicChoiceRatio;
    const revisitRatio = player.totalSteps > 0 ? player.revisitCount / player.totalSteps : 0;
    const explorationRate = player.explorationRate;

    let dfsScore = deadEndRatio * 48 + unexploredRatio * 34 + Math.min(1, revisitRatio * 2) * 18;
    let bfsScore =
      (1 - Math.min(1, diffRatio)) * 62 +
      (1 - Math.min(1, revisitRatio * 2)) * 20 +
      Math.min(1, explorationRate / 70) * 18;
    let linearScore =
      systematicRatio * 55 + (1 - unexploredRatio) * 25 + Math.min(1, revisitRatio * 1.5) * 20;

    dfsScore = Math.round(Math.max(0, Math.min(100, dfsScore)));
    bfsScore = Math.round(Math.max(0, Math.min(100, bfsScore)));
    linearScore = Math.round(Math.max(0, Math.min(100, linearScore)));

    const scores = { D: dfsScore, B: bfsScore, L: linearScore };
    const dominant = Object.keys(scores).reduce((a, b) => (scores[a] >= scores[b] ? a : b));
    let typeCode = dominant;
    if (dfsScore >= 65 && bfsScore >= 65 && linearScore >= 65) typeCode = "X";

    const titleIndex = randInt(this.TITLE_POOL[typeCode].length);
    const commentIndex = randInt(this.COMMENT_POOL[typeCode].length);

    return {
      dfsScore,
      bfsScore,
      linearScore,
      typeCode,
      titleIndex,
      commentIndex,
      title: this.TITLE_POOL[typeCode][titleIndex],
      comment: this.COMMENT_POOL[typeCode][commentIndex],
      stats: {
        totalSteps: player.totalSteps,
        idealSteps,
        stepDiff: player.stepDiff,
        explorationRate: Math.round(explorationRate),
        elapsedSeconds: Math.round(player.elapsedSeconds),
      },
    };
  },

  /** typeCode + variant番号から称号・コメントを復元する（QRカード表示用） */
  reconstruct(typeCode, titleIndex, commentIndex) {
    const titles = this.TITLE_POOL[typeCode] || this.TITLE_POOL.X;
    const comments = this.COMMENT_POOL[typeCode] || this.COMMENT_POOL.X;
    return {
      title: titles[titleIndex % titles.length] || titles[0],
      comment: comments[commentIndex % comments.length] || comments[0],
    };
  },
};


/* ================================================================
   StorageManager
   ----------------------------------------------------------------
   診断結果の保存・集計を担当する。今はブラウザのlocalStorageに
   保存しているが、メソッドはすべて async にしてあるため、将来
   Firebase等のオンラインDBに差し替える場合も、このクラスの中身だけ
   を書き換えれば他のコードには影響しない設計になっている。
================================================================ */
class StorageManager {
  constructor() {
    this.storageKey = "algo_lab_results_v1";
    this.maxRecords = 2000; // 肥大化防止のため保存件数に上限を設ける
    this.available = this._checkAvailable();
  }

  _checkAvailable() {
    try {
      const testKey = "__algo_lab_test__";
      localStorage.setItem(testKey, "1");
      localStorage.removeItem(testKey);
      return true;
    } catch (e) {
      // プライベートブラウジング等でlocalStorageが使えない場合の保険
      console.warn("localStorageが利用できないため、統計は保存されません。", e);
      return false;
    }
  }

  /** 1件の診断結果を保存する */
  async saveResult(record) {
    if (!this.available) return null;
    const all = await this.getAllResults();
    all.push(record);
    const trimmed = all.slice(-this.maxRecords);
    try {
      localStorage.setItem(this.storageKey, JSON.stringify(trimmed));
    } catch (e) {
      console.warn("結果の保存に失敗しました。", e);
    }
    return record;
  }

  /** 保存済みの全結果を取得する */
  async getAllResults() {
    if (!this.available) return [];
    try {
      const raw = localStorage.getItem(this.storageKey);
      return raw ? JSON.parse(raw) : [];
    } catch (e) {
      return [];
    }
  }

  /** IDから1件だけ取得する（同一端末内での照合に利用） */
  async getResultById(id) {
    const all = await this.getAllResults();
    return all.find((r) => r.id === id) || null;
  }

  /** 集計統計（歴代人数・平均値・タイプ割合・各種ランキング）を計算する */
  async getAggregateStats() {
    const all = await this.getAllResults();
    if (all.length === 0) {
      return {
        totalPlayers: 0,
        avgTime: 0,
        avgSteps: 0,
        typeRatio: { D: 0, B: 0, L: 0, X: 0 },
        titleRanking: [],
        fastestRanking: [],
        explorationRanking: [],
      };
    }
    const totalPlayers = all.length;
    const avgTime = all.reduce((s, r) => s + r.elapsedSeconds, 0) / totalPlayers;
    const avgSteps = all.reduce((s, r) => s + r.steps, 0) / totalPlayers;

    const typeCounts = { D: 0, B: 0, L: 0, X: 0 };
    all.forEach((r) => { typeCounts[r.typeCode] = (typeCounts[r.typeCode] || 0) + 1; });
    const typeRatio = {};
    Object.keys(typeCounts).forEach((k) => {
      typeRatio[k] = Math.round((typeCounts[k] / totalPlayers) * 100);
    });

    const titleCounts = {};
    all.forEach((r) => { titleCounts[r.title] = (titleCounts[r.title] || 0) + 1; });
    const titleRanking = Object.entries(titleCounts)
      .sort((a, b) => b[1] - a[1])
      .slice(0, 10)
      .map(([title, count]) => ({ title, count }));

    const fastestRanking = [...all].sort((a, b) => a.elapsedSeconds - b.elapsedSeconds).slice(0, 10);
    const explorationRanking = [...all].sort((a, b) => b.explorationRate - a.explorationRate).slice(0, 10);

    return { totalPlayers, avgTime, avgSteps, typeRatio, titleRanking, fastestRanking, explorationRanking };
  }
}


/* ================================================================
   SimpleQR（QRコード符号化エンジン）
   ----------------------------------------------------------------
   外部ライブラリを使わずに実装した、最小限のQRコードエンコーダー。
   対応範囲：型番(バージョン)1〜5・誤り訂正レベルL・バイトモードのみ・
   マスクパターンは固定(0)。文化祭展示用途として十分なデータ量
   （最大108バイト程度）を想定した割り切り実装。
================================================================ */
const QR_EXP_TABLE = new Array(256);
const QR_LOG_TABLE = new Array(256);
(function buildGaloisTables() {
  for (let i = 0; i < 8; i++) QR_EXP_TABLE[i] = 1 << i;
  for (let i = 8; i < 256; i++) {
    QR_EXP_TABLE[i] =
      QR_EXP_TABLE[i - 4] ^ QR_EXP_TABLE[i - 5] ^ QR_EXP_TABLE[i - 6] ^ QR_EXP_TABLE[i - 8];
  }
  for (let i = 0; i < 255; i++) QR_LOG_TABLE[QR_EXP_TABLE[i]] = i;
})();

function qrGexp(n) {
  let m = n;
  while (m < 0) m += 255;
  while (m >= 255) m -= 255;
  return QR_EXP_TABLE[m];
}
function qrPolyMultiply(a, b) {
  const result = new Array(a.length + b.length - 1).fill(0);
  for (let i = 0; i < a.length; i++) {
    if (a[i] === 0) continue;
    for (let j = 0; j < b.length; j++) {
      if (b[j] === 0) continue;
      result[i + j] ^= qrGexp(QR_LOG_TABLE[a[i]] + QR_LOG_TABLE[b[j]]);
    }
  }
  return result;
}
function qrGeneratorPolynomial(ecCount) {
  let poly = [1];
  for (let i = 0; i < ecCount; i++) poly = qrPolyMultiply(poly, [1, qrGexp(i)]);
  return poly;
}
function qrRsEncode(dataCodewords, ecCount) {
  const generator = qrGeneratorPolynomial(ecCount);
  const remainder = dataCodewords.concat(new Array(ecCount).fill(0));
  for (let i = 0; i < dataCodewords.length; i++) {
    const coef = remainder[i];
    if (coef === 0) continue;
    const logCoef = QR_LOG_TABLE[coef];
    for (let j = 0; j < generator.length; j++) {
      remainder[i + j] ^= qrGexp(logCoef + QR_LOG_TABLE[generator[j]]);
    }
  }
  return remainder.slice(dataCodewords.length);
}

const QR_FORMAT_GENERATOR = 0b10100110111;
const QR_FORMAT_MASK = 0b101010000010010;
function qrBitLength(n) {
  let len = 0, v = n;
  while (v !== 0) { len++; v >>>= 1; }
  return len;
}
function qrGetFormatBits(data5bit) {
  let d = data5bit << 10;
  const gLen = qrBitLength(QR_FORMAT_GENERATOR);
  while (qrBitLength(d) - gLen >= 0) {
    d ^= QR_FORMAT_GENERATOR << (qrBitLength(d) - gLen);
  }
  return ((data5bit << 10) | d) ^ QR_FORMAT_MASK;
}
function qrPushBits(arr, value, len) {
  for (let i = len - 1; i >= 0; i--) arr.push((value >> i) & 1);
}

class SimpleQR {
  constructor(text) {
    this.text = text;
    this._build();
  }

  _build() {
    const fullBytes = Array.from(new TextEncoder().encode(this.text));
    let bytes = fullBytes;
    let version = null;

    for (const v of Object.keys(SimpleQR.VERSIONS).map(Number).sort((a, b) => a - b)) {
      const cap = SimpleQR.VERSIONS[v];
      const neededBits = 4 + 8 + bytes.length * 8;
      if (neededBits <= cap.data * 8) { version = v; break; }
    }
    if (version === null) {
      version = 5;
      const cap = SimpleQR.VERSIONS[5];
      const maxPayloadBytes = Math.floor((cap.data * 8 - 12) / 8);
      bytes = fullBytes.slice(0, Math.max(1, maxPayloadBytes));
    }

    this.version = version;
    const cap = SimpleQR.VERSIONS[version];
    this.size = cap.size;

    const bits = [];
    qrPushBits(bits, 0b0100, 4);
    qrPushBits(bits, bytes.length, 8);
    for (const b of bytes) qrPushBits(bits, b, 8);

    const maxBits = cap.data * 8;
    const terminatorLen = Math.max(0, Math.min(4, maxBits - bits.length));
    qrPushBits(bits, 0, terminatorLen);
    while (bits.length % 8 !== 0) bits.push(0);

    const padBytes = [0xec, 0x11];
    let padIndex = 0;
    while (bits.length / 8 < cap.data) {
      qrPushBits(bits, padBytes[padIndex % 2], 8);
      padIndex++;
    }

    const dataCodewords = [];
    for (let i = 0; i < bits.length; i += 8) {
      let byte = 0;
      for (let j = 0; j < 8; j++) byte = (byte << 1) | bits[i + j];
      dataCodewords.push(byte);
    }

    const ecCodewords = qrRsEncode(dataCodewords, cap.ec);
    const allCodewords = dataCodewords.concat(ecCodewords);
    const allBits = [];
    for (const cw of allCodewords) qrPushBits(allBits, cw, 8);

    this._initMatrix();
    this._placeFunctionPatterns();
    this._placeDataBits(allBits);
    this._applyMaskAndFormat();
  }

  _initMatrix() {
    this.modules = Array.from({ length: this.size }, () => new Array(this.size).fill(0));
    this.isFunction = Array.from({ length: this.size }, () => new Array(this.size).fill(false));
  }
  _setFunc(r, c, dark) {
    if (r < 0 || r >= this.size || c < 0 || c >= this.size) return;
    this.modules[r][c] = dark ? 1 : 0;
    this.isFunction[r][c] = true;
  }
  _placeFinderAt(r0, c0) {
    for (let r = -1; r <= 7; r++) {
      for (let c = -1; c <= 7; c++) {
        const rr = r0 + r, cc = c0 + c;
        if (rr < 0 || rr >= this.size || cc < 0 || cc >= this.size) continue;
        let dark = false;
        if (r >= 0 && r <= 6 && c >= 0 && c <= 6 && (r === 0 || r === 6 || c === 0 || c === 6)) dark = true;
        else if (r >= 2 && r <= 4 && c >= 2 && c <= 4) dark = true;
        this._setFunc(rr, cc, dark);
      }
    }
  }
  _placeFunctionPatterns() {
    this._placeFinderAt(0, 0);
    this._placeFinderAt(0, this.size - 7);
    this._placeFinderAt(this.size - 7, 0);

    for (let i = 8; i < this.size - 8; i++) {
      const dark = i % 2 === 0;
      if (!this.isFunction[6][i]) this._setFunc(6, i, dark);
      if (!this.isFunction[i][6]) this._setFunc(i, 6, dark);
    }

    const center = SimpleQR.ALIGNMENT_CENTER[this.version];
    if (center) {
      const [ar, ac] = center;
      for (let r = -2; r <= 2; r++) {
        for (let c = -2; c <= 2; c++) {
          const dark = Math.max(Math.abs(r), Math.abs(c)) !== 1;
          this._setFunc(ar + r, ac + c, dark);
        }
      }
    }

    for (let i = 0; i < 9; i++) {
      if (!this.isFunction[8][i]) this._setFunc(8, i, false);
      if (!this.isFunction[i][8]) this._setFunc(i, 8, false);
    }
    for (let i = 0; i < 8; i++) {
      this._setFunc(this.size - 1 - i, 8, false);
      this._setFunc(8, this.size - 1 - i, false);
    }
    this._setFunc(this.size - 8, 8, true);
  }
  _placeDataBits(bitStream) {
    let bitIndex = 0;
    let dir = -1;
    let col = this.size - 1;
    while (col > 0) {
      if (col === 6) col--;
      for (let i = 0; i < this.size; i++) {
        const row = dir < 0 ? this.size - 1 - i : i;
        for (let cOff = 0; cOff < 2; cOff++) {
          const c = col - cOff;
          if (this.isFunction[row][c]) continue;
          const bit = bitIndex < bitStream.length ? bitStream[bitIndex] : 0;
          bitIndex++;
          this.modules[row][c] = bit;
        }
      }
      dir = -dir;
      col -= 2;
    }
  }
  _applyMaskAndFormat() {
    for (let r = 0; r < this.size; r++) {
      for (let c = 0; c < this.size; c++) {
        if (this.isFunction[r][c]) continue;
        const maskBit = (r + c) % 2 === 0 ? 1 : 0;
        this.modules[r][c] = this.modules[r][c] ^ maskBit;
      }
    }
    const ECL_L = 0b01;
    const maskId = 0;
    const formatData = (ECL_L << 3) | maskId;
    const formatBits = qrGetFormatBits(formatData);
    for (let i = 0; i < 15; i++) {
      const bit = (formatBits >> i) & 1;
      if (i < 6) this.modules[i][8] = bit;
      else if (i < 8) this.modules[i + 1][8] = bit;
      else this.modules[this.size - 15 + i][8] = bit;
      if (i < 8) this.modules[8][this.size - i - 1] = bit;
      else if (i < 9) this.modules[8][15 - i] = bit;
      else this.modules[8][14 - i] = bit;
    }
    this.modules[this.size - 8][8] = 1;
  }
  renderToCanvas(canvas, scale = 6, quiet = 4) {
    const total = this.size + quiet * 2;
    canvas.width = total * scale;
    canvas.height = total * scale;
    const ctx = canvas.getContext("2d");
    ctx.fillStyle = "#ffffff";
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = "#0a0e17";
    for (let r = 0; r < this.size; r++) {
      for (let c = 0; c < this.size; c++) {
        if (this.modules[r][c]) ctx.fillRect((c + quiet) * scale, (r + quiet) * scale, scale, scale);
      }
    }
  }
}
SimpleQR.VERSIONS = {
  1: { data: 19, ec: 7, size: 21 },
  2: { data: 34, ec: 10, size: 25 },
  3: { data: 55, ec: 15, size: 29 },
  4: { data: 80, ec: 20, size: 33 },
  5: { data: 108, ec: 26, size: 37 },
};
SimpleQR.ALIGNMENT_CENTER = { 2: [18, 18], 3: [22, 22], 4: [26, 26], 5: [30, 30] };


/* ================================================================
   QRManager
   ----------------------------------------------------------------
   診断カードのURL組み立て・QRコード生成・画面への描画、および
   QR経由でアクセスされた際のパラメータ解析を担当する。
   ----------------------------------------------------------------
   【修正のポイント】
   以前はURLの「#(ハッシュ)」部分にデータを載せていたが、QR読み取り
   アプリや一部ブラウザの組み合わせによってはハッシュ部分が引き継がれず
   「読み取れるのに何も表示されない」という不具合につながっていた。
   ハッシュはあくまでクライアント側だけの情報として扱われることが
   多く、外部アプリ間の受け渡しで欠落しやすいため、より互換性が高い
   「?(クエリパラメータ)」方式に変更している。
   また、GitHub Pages等にアップロードした場合でも正しく動くよう、
   現在表示中のページの origin + pathname を基準にURLを組み立てる
   （相対パスやローカルファイルパスに依存しない）。
   将来オンライン保存に対応する場合は、id パラメータだけを渡し、
   QRManager.parseCardParams() の中で「idからサーバーに問い合わせる」
   処理へ差し替えれば良いように、idも必ず同梱している。
================================================================ */
const QRManager = {
  // QRコード(型番1〜5)は最大でも108バイト程度しか収まらないため、
  // ペイロードは必要最小限に絞り込む。「id」はローカル保存の照合キー
  // としては便利だが、QRコードのURLに載せる必須情報ではないため含めない
  // （URLが長くなり、長いGitHub Pagesのパスと合わさると入り切らなくなる
  //   おそれがあるため）。将来オンライン保存に対応する場合は、下記の
  //   ように「id」だけを載せる軽量な形式に切り替えれば良い設計にしている。
  // QRコード(型番1〜5・レベルL)に安全に収まる上限バイト数。
  // 規格上の最大は108バイトだが、余裕を持って100バイトを基準にする。
  QR_SAFE_BYTE_LIMIT: 100,

  /** location.origin + location.pathname から「まっさらなベースURL」を作る（末尾のindex.htmlは短縮のため省く） */
  _buildBaseUrl() {
    let base = location.origin + location.pathname;
    if (base.endsWith("/index.html")) base = base.slice(0, -"index.html".length);
    return base;
  },

  /** 診断結果レコードから、診断カードを直接開けるURLを組み立てる */
  buildCardUrl(record) {
    const base = this._buildBaseUrl();

    const params = new URLSearchParams();
    params.set("ty", record.typeCode);
    params.set("ti", record.titleIndex);
    params.set("ci", record.commentIndex);
    params.set("d", record.dfsScore);
    params.set("b", record.bfsScore);
    params.set("l", record.linearScore);
    params.set("tm", record.elapsedSeconds);
    params.set("st", record.steps);
    params.set("pid", record.pid);
    const fullUrl = `${base}?${params.toString()}`;
    if (new TextEncoder().encode(fullUrl).length <= this.QR_SAFE_BYTE_LIMIT) {
      return fullUrl;
    }

    // 診断データ全部だと収まらない長いホスティングパスの場合は、将来の
    // オンライン化を見据えた「idだけを渡す」軽量URLにフォールバックする
    if (record.id) {
      const shortParams = new URLSearchParams();
      shortParams.set("id", record.id);
      const shortUrl = `${base}?${shortParams.toString()}`;
      if (new TextEncoder().encode(shortUrl).length <= this.QR_SAFE_BYTE_LIMIT) {
        return shortUrl;
      }
    }
    // それでも収まらない場合（非常に長いホスティングパス等）は、そのまま返す。
    // renderInto側でQRコード化を諦め、URLをテキストリンクとして表示する。
    return fullUrl;
  },

  /** location.search からカード情報を復元する。カード情報が無ければ null */
  parseCardParams(search) {
    const params = new URLSearchParams(search);
    // 「ty」と「pid」の両方があれば、診断データがそのままURLに載っている形式
    if (params.get("ty") && params.get("pid")) {
      return {
        typeCode: params.get("ty") || "X",
        titleIndex: parseInt(params.get("ti") || "0", 10),
        commentIndex: parseInt(params.get("ci") || "0", 10),
        dfsScore: params.get("d") || "0",
        bfsScore: params.get("b") || "0",
        linearScore: params.get("l") || "0",
        elapsedSeconds: parseInt(params.get("tm") || "0", 10),
        steps: params.get("st") || "0",
        pid: params.get("pid") || "------",
        id: params.get("id") || "",
      };
    }
    // 「id」だけの軽量形式の場合は、呼び出し側でStorageManagerから引き当てる
    if (params.get("id")) {
      return { idOnly: true, id: params.get("id") };
    }
    return null;
  },

  /** QRコードを生成し、指定した要素に描画する（失敗しても画面を壊さない） */
  renderInto(wrapEl, fallbackEl, url) {
    wrapEl.innerHTML = "";
    fallbackEl.classList.add("hidden");

    const byteLength = new TextEncoder().encode(url).length;
    if (byteLength > this.QR_SAFE_BYTE_LIMIT) {
      // ここでQRコード化すると内部で自動的に切り詰められ「読み取れるのに
      // 何も表示されない（＝壊れたURL）」QRコードになってしまうため、
      // 無理にQR化はせず、URLをそのままテキストリンクとして案内する。
      console.warn("URLが長すぎるためQRコード化を見送り、テキストリンクを表示します。");
      fallbackEl.textContent = url;
      fallbackEl.classList.remove("hidden");
      return;
    }

    try {
      const qr = new SimpleQR(url);
      const canvas = document.createElement("canvas");
      qr.renderToCanvas(canvas, 5);
      wrapEl.appendChild(canvas);
      fallbackEl.textContent = url;
    } catch (err) {
      // QR生成に失敗しても、URLをテキストで表示する代替表示にすることで
      // 「エラーで画面が壊れる」ことだけは絶対に避ける
      console.error("QR生成に失敗しました:", err);
      fallbackEl.textContent = url;
      fallbackEl.classList.remove("hidden");
    }
  },
};


/* ================================================================
   Renderer（キャンバス描画の共通処理）
================================================================ */
const Renderer = {
  /** ダンジョン本体を描画する（探索済みマスのみ表示＝霧効果） */
  drawDungeon(ctx, maze, revealedSet, player, cellPx) {
    const w = maze.cols * cellPx;
    const h = maze.rows * cellPx;
    ctx.clearRect(0, 0, w, h);
    ctx.fillStyle = "#01030a";
    ctx.fillRect(0, 0, w, h);

    for (let r = 0; r < maze.rows; r++) {
      for (let c = 0; c < maze.cols; c++) {
        const key = cellKey(c, r);
        if (!revealedSet.has(key)) continue;
        const x = c * cellPx;
        const y = r * cellPx;
        const cell = maze.cellAt(c, r);

        ctx.fillStyle = "#101a30";
        ctx.fillRect(x + 2, y + 2, cellPx - 4, cellPx - 4);

        ctx.strokeStyle = "#3a4a75";
        ctx.lineWidth = 3;
        ctx.beginPath();
        if (cell.N) { ctx.moveTo(x, y); ctx.lineTo(x + cellPx, y); }
        if (cell.S) { ctx.moveTo(x, y + cellPx); ctx.lineTo(x + cellPx, y + cellPx); }
        if (cell.W) { ctx.moveTo(x, y); ctx.lineTo(x, y + cellPx); }
        if (cell.E) { ctx.moveTo(x + cellPx, y); ctx.lineTo(x + cellPx, y + cellPx); }
        ctx.stroke();

        // 宝箱：取得済みなら消して「取得したこと」が誰でも分かるようにする
        if (c === maze.treasure.c && r === maze.treasure.r && !player.treasureCollected) {
          ctx.fillStyle = "#ffce54";
          ctx.fillRect(x + cellPx * 0.28, y + cellPx * 0.36, cellPx * 0.44, cellPx * 0.34);
          ctx.fillStyle = "#8a6a1d";
          ctx.fillRect(x + cellPx * 0.28, y + cellPx * 0.36, cellPx * 0.44, cellPx * 0.08);
        }
        // ゴール：宝箱と間違えないよう、チェック柄のRPG風フラッグにする
        if (c === maze.goal.c && r === maze.goal.r) {
          Renderer._drawGoalFlag(ctx, x, y, cellPx);
        }
      }
    }

    // プレイヤー（ピクセル風の四角＋目）
    const px = player.drawC * cellPx;
    const py = player.drawR * cellPx;
    ctx.fillStyle = "#4deeea";
    ctx.fillRect(px + cellPx * 0.22, py + cellPx * 0.18, cellPx * 0.56, cellPx * 0.64);
    ctx.fillStyle = "#0a0e17";
    ctx.fillRect(px + cellPx * 0.34, py + cellPx * 0.36, cellPx * 0.1, cellPx * 0.1);
    ctx.fillRect(px + cellPx * 0.56, py + cellPx * 0.36, cellPx * 0.1, cellPx * 0.1);

    // 宝箱を持っている間は、頭上に小さな目印を表示する（見た目でも取得済みと分かるように）
    if (player.treasureCollected) {
      ctx.fillStyle = "#ffce54";
      ctx.fillRect(px + cellPx * 0.36, py - cellPx * 0.06, cellPx * 0.28, cellPx * 0.16);
    }
  },

  /** RPG風のゴール旗（チェック柄）を描く。宝箱（四角い箱）とはっきり区別できる見た目にする */
  _drawGoalFlag(ctx, x, y, cellPx) {
    const poleX = x + cellPx * 0.32;
    const poleTopY = y + cellPx * 0.16;
    const poleBottomY = y + cellPx * 0.86;

    // 旗ざお
    ctx.strokeStyle = "#d8d2c2";
    ctx.lineWidth = Math.max(2, cellPx * 0.06);
    ctx.beginPath();
    ctx.moveTo(poleX, poleTopY);
    ctx.lineTo(poleX, poleBottomY);
    ctx.stroke();

    // 旗（チェック柄でゴールらしさを演出）
    const flagW = cellPx * 0.4;
    const flagH = cellPx * 0.28;
    const half = flagH / 2;
    const halfW = flagW / 2;
    ctx.fillStyle = "#4deeea";
    ctx.fillRect(poleX, poleTopY, flagW, flagH);
    ctx.fillStyle = "#0a0e17";
    ctx.fillRect(poleX, poleTopY, halfW, half);
    ctx.fillRect(poleX + halfW, poleTopY + half, halfW, half);

    // 台座
    ctx.fillStyle = "#26314f";
    ctx.fillRect(poleX - cellPx * 0.08, poleBottomY - cellPx * 0.03, cellPx * 0.24, cellPx * 0.06);
  },

  /** ミニマップ描画：全体像を薄く、探索済み＆プレイヤーを強調 */
  drawMinimap(ctx, maze, revealedSet, player) {
    const w = ctx.canvas.width;
    const h = ctx.canvas.height;
    ctx.clearRect(0, 0, w, h);
    const cw = w / maze.cols;
    const ch = h / maze.rows;

    for (let r = 0; r < maze.rows; r++) {
      for (let c = 0; c < maze.cols; c++) {
        const key = cellKey(c, r);
        const revealed = revealedSet.has(key);
        ctx.fillStyle = revealed ? "rgba(77,238,234,0.35)" : "rgba(255,255,255,0.05)";
        ctx.fillRect(c * cw, r * ch, cw - 1, ch - 1);
      }
    }
    if (revealedSet.has(cellKey(maze.treasure.c, maze.treasure.r)) && !player.treasureCollected) {
      ctx.fillStyle = "#ffce54";
      ctx.fillRect(maze.treasure.c * cw, maze.treasure.r * ch, cw - 1, ch - 1);
    }
    if (revealedSet.has(cellKey(maze.goal.c, maze.goal.r))) {
      ctx.fillStyle = "#4deeea";
      ctx.fillRect(maze.goal.c * cw, maze.goal.r * ch, cw - 1, ch - 1);
    }
    ctx.fillStyle = "#ff2e6d";
    ctx.fillRect(player.drawC * cw, player.drawR * ch, cw - 1, ch - 1);
  },

  /** 結果画面：迷路の外形＋ルートを描画する（経路比較用） */
  drawRoute(canvas, maze, path, color) {
    const ctx = canvas.getContext("2d");
    const size = canvas.clientWidth || 200;
    canvas.width = size;
    canvas.height = size;
    const cellPx = size / Math.max(maze.cols, maze.rows);

    ctx.clearRect(0, 0, size, size);
    ctx.fillStyle = "#01030a";
    ctx.fillRect(0, 0, size, size);

    ctx.strokeStyle = "#26314f";
    ctx.lineWidth = 1;
    for (let r = 0; r < maze.rows; r++) {
      for (let c = 0; c < maze.cols; c++) {
        const cell = maze.cellAt(c, r);
        const x = c * cellPx;
        const y = r * cellPx;
        ctx.beginPath();
        if (cell.N) { ctx.moveTo(x, y); ctx.lineTo(x + cellPx, y); }
        if (cell.S) { ctx.moveTo(x, y + cellPx); ctx.lineTo(x + cellPx, y + cellPx); }
        if (cell.W) { ctx.moveTo(x, y); ctx.lineTo(x, y + cellPx); }
        if (cell.E) { ctx.moveTo(x + cellPx, y); ctx.lineTo(x + cellPx, y + cellPx); }
        ctx.stroke();
      }
    }

    ctx.strokeStyle = color;
    ctx.lineWidth = Math.max(2, cellPx * 0.12);
    ctx.lineJoin = "round";
    ctx.beginPath();
    path.forEach((p, i) => {
      const x = p.c * cellPx + cellPx / 2;
      const y = p.r * cellPx + cellPx / 2;
      if (i === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    });
    ctx.stroke();

    const start = path[0];
    const end = path[path.length - 1];
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.arc(start.c * cellPx + cellPx / 2, start.r * cellPx + cellPx / 2, cellPx * 0.18, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillRect(end.c * cellPx + cellPx * 0.32, end.r * cellPx + cellPx * 0.32, cellPx * 0.36, cellPx * 0.36);
  },
};


/* ================================================================
   UIManager
   ----------------------------------------------------------------
   画面切り替え・HUD更新・ポップアップ・REC表示などのDOM操作を
   一手に引き受けるクラス。GameManagerからは「何を表示したいか」だけを
   伝えてもらい、実際のDOM操作の詳細はすべてここに閉じ込める。
================================================================ */
class UIManager {
  showScreen(screenId) {
    document.querySelectorAll(".screen").forEach((el) => {
      if (el.id === screenId) el.classList.add("active");
      else el.classList.remove("active");
    });
  }

  updateSteps(steps) {
    document.getElementById("hud-steps").textContent = steps;
  }
  updateTimer(seconds) {
    document.getElementById("hud-timer").textContent = formatTime(seconds);
  }
  updateMission(text) {
    document.getElementById("hud-mission").textContent = text;
  }

  /** 宝箱の取得状況を、バッジ表示とポップアップの両方ではっきり伝える */
  setTreasureAcquired(acquired) {
    const badge = document.getElementById("treasure-badge");
    const badgeText = document.getElementById("treasure-badge-text");
    if (acquired) {
      badge.classList.add("acquired");
      badgeText.textContent = "宝箱：取得済み";
    } else {
      badge.classList.remove("acquired");
      badgeText.textContent = "宝箱：未取得";
    }
  }
  showTreasurePopup() {
    const popup = document.getElementById("treasure-popup");
    popup.classList.remove("hidden");
    // アニメーションを毎回最初から再生させるためのリフロー強制
    popup.classList.remove("show");
    void popup.offsetWidth;
    popup.classList.add("show");
    setTimeout(() => {
      popup.classList.add("hidden");
      popup.classList.remove("show");
    }, 1800);
  }

  showFloatingMessage(text) {
    const el = document.getElementById("floating-message");
    el.textContent = text;
    el.classList.remove("hidden");
    el.style.animation = "none";
    void el.offsetWidth;
    el.style.animation = "";
  }

  /** ゲーム開始時：録画中(赤・点滅)の表示にする */
  setRecRecording() {
    const el = document.getElementById("rec-indicator");
    el.classList.remove("hidden", "stopped");
    document.getElementById("rec-text").textContent = "REC ● OBSERVING";
  }
  /** クリア後：録画終了(グレー)の表示に切り替える */
  setRecStopped() {
    const el = document.getElementById("rec-indicator");
    el.classList.remove("hidden");
    el.classList.add("stopped");
    document.getElementById("rec-text").textContent = "REC ■ ANALYSIS DONE";
  }
  hideRec() {
    document.getElementById("rec-indicator").classList.add("hidden");
  }

  showLabBadge(subjectId) {
    document.getElementById("lab-id-number").textContent = subjectId;
    document.getElementById("lab-id-badge").classList.remove("hidden");
  }
  hideLabBadge() {
    document.getElementById("lab-id-badge").classList.add("hidden");
  }

  /** クリア後の「解析中」演出（データ収集→解析→プログレスバー→解析完了） */
  playAnalyzingSequence() {
    return new Promise((resolve) => {
      this.showScreen("screen-analyzing");
      const line = document.getElementById("analyzing-line");
      const bar = document.getElementById("progress-bar");
      const percentText = document.getElementById("analyzing-percent");
      const messages = ["データ収集中...", "解析中...", "思考パターンを照合中...", "解析完了"];
      let msgIndex = 0;
      line.textContent = messages[0];
      bar.style.width = "0%";
      percentText.textContent = "0%";

      const totalDurationMs = 3000;
      const startTime = performance.now();

      const msgInterval = setInterval(() => {
        msgIndex++;
        if (msgIndex < messages.length) line.textContent = messages[msgIndex];
      }, totalDurationMs / messages.length);

      const tick = () => {
        const elapsed = performance.now() - startTime;
        const pct = Math.min(100, Math.round((elapsed / totalDurationMs) * 100));
        bar.style.width = pct + "%";
        percentText.textContent = pct + "%";
        if (elapsed < totalDurationMs) {
          requestAnimationFrame(tick);
        } else {
          clearInterval(msgInterval);
          line.textContent = "解析完了";
          bar.style.width = "100%";
          percentText.textContent = "100%";
          setTimeout(resolve, 400);
        }
      };
      requestAnimationFrame(tick);
    });
  }
}


/* ================================================================
   ResultRenderer
   ----------------------------------------------------------------
   診断結果画面・統計ページ・診断カード画面へのデータ描画をまとめて
   担当する。GameManagerからデータを受け取り、DOMへ反映するだけの
   「見た目専門」のクラス。
================================================================ */
class ResultRenderer {
  /** 診断結果画面を描画する */
  renderResult(record, maze, player) {
    document.getElementById("result-title").textContent = record.title;
    document.getElementById("result-ai-comment").textContent = record.comment;
    document.getElementById("result-subject-id").textContent = record.pid;

    this._animateBar("bar-dfs", "pct-dfs", record.dfsScore);
    this._animateBar("bar-bfs", "pct-bfs", record.bfsScore);
    this._animateBar("bar-linear", "pct-linear", record.linearScore);

    document.getElementById("stat-time").textContent = formatTime(record.elapsedSeconds);
    document.getElementById("stat-steps").textContent = record.steps;
    const diff = record.stepDiff;
    document.getElementById("stat-diff").textContent = (diff >= 0 ? "+" : "") + diff;
    document.getElementById("stat-rate").textContent = record.explorationRate + "%";

    const shortestPath = maze
      .shortestPath(maze.start, maze.treasure)
      .concat(maze.shortestPath(maze.treasure, maze.goal).slice(1));
    const dfsPath = maze.simulateDFSPath(maze.start, maze.goal);

    Renderer.drawRoute(document.getElementById("route-canvas-player"), maze, player.path, "#4deeea");
    Renderer.drawRoute(document.getElementById("route-canvas-shortest"), maze, shortestPath, "#ffce54");
    Renderer.drawRoute(document.getElementById("route-canvas-dfs"), maze, dfsPath, "#ff2e6d");
  }

  _animateBar(barId, pctId, value) {
    const bar = document.getElementById(barId);
    const pct = document.getElementById(pctId);
    requestAnimationFrame(() => { bar.style.width = value + "%"; });
    let current = 0;
    const step = () => {
      current += Math.max(1, Math.round((value - current) / 6));
      if (current >= value) current = value;
      pct.textContent = current + "%";
      if (current < value) requestAnimationFrame(step);
    };
    step();
  }

  /** 診断カード画面（QR読み取り後）を描画する */
  renderCard(cardData) {
    const { title, comment } = Analyzer.reconstruct(cardData.typeCode, cardData.titleIndex, cardData.commentIndex);
    document.getElementById("card-title").textContent = title;
    document.getElementById("card-comment").textContent = comment;
    document.getElementById("card-player-id").textContent = cardData.pid;
    document.getElementById("card-stat-time").textContent = formatTime(cardData.elapsedSeconds);
    document.getElementById("card-stat-steps").textContent = cardData.steps;

    document.getElementById("card-bar-dfs").style.width = cardData.dfsScore + "%";
    document.getElementById("card-pct-dfs").textContent = cardData.dfsScore + "%";
    document.getElementById("card-bar-bfs").style.width = cardData.bfsScore + "%";
    document.getElementById("card-pct-bfs").textContent = cardData.bfsScore + "%";
    document.getElementById("card-bar-linear").style.width = cardData.linearScore + "%";
    document.getElementById("card-pct-linear").textContent = cardData.linearScore + "%";
  }

  /** 「みんなの統計」ページを描画する */
  renderStats(stats) {
    document.getElementById("stats-total-players").textContent = stats.totalPlayers;
    document.getElementById("stats-avg-time").textContent = formatTime(stats.avgTime);
    document.getElementById("stats-avg-steps").textContent = Math.round(stats.avgSteps);

    document.getElementById("stats-bar-dfs").style.width = stats.typeRatio.D + "%";
    document.getElementById("stats-pct-dfs").textContent = stats.typeRatio.D + "%";
    document.getElementById("stats-bar-bfs").style.width = stats.typeRatio.B + "%";
    document.getElementById("stats-pct-bfs").textContent = stats.typeRatio.B + "%";
    document.getElementById("stats-bar-linear").style.width = stats.typeRatio.L + "%";
    document.getElementById("stats-pct-linear").textContent = stats.typeRatio.L + "%";

    this._renderRankingList(
      "stats-title-ranking",
      stats.titleRanking,
      (item) => `<span class="rank-name">${item.title}</span><span class="rank-value">${item.count}人</span>`
    );
    this._renderRankingList(
      "stats-fastest-ranking",
      stats.fastestRanking,
      (item) => `<span class="rank-name">${item.pid ? "被験者" + item.pid : "被験者"}（${item.title}）</span><span class="rank-value">${formatTime(item.elapsedSeconds)}</span>`
    );
    this._renderRankingList(
      "stats-exploration-ranking",
      stats.explorationRanking,
      (item) => `<span class="rank-name">${item.pid ? "被験者" + item.pid : "被験者"}（${item.title}）</span><span class="rank-value">${item.explorationRate}%</span>`
    );
  }

  _renderRankingList(elementId, items, lineBuilder) {
    const el = document.getElementById(elementId);
    if (!items || items.length === 0) {
      el.innerHTML = `<li class="ranking-empty">まだ記録がありません。最初のデータ提供者になろう！</li>`;
      return;
    }
    el.innerHTML = items.map((item) => `<li>${lineBuilder(item)}</li>`).join("");
  }
}


/* ================================================================
   GameManager
   ----------------------------------------------------------------
   すべてのクラスをつなぎ合わせ、タイトル→ゲーム→解析演出→結果→統計
   という一連の流れを制御する司令塔。
================================================================ */
class GameManager {
  constructor() {
    this.COLS = 11;
    this.ROWS = 9;

    this.ui = new UIManager();
    this.storage = new StorageManager();
    this.resultRenderer = new ResultRenderer();

    this.maze = null;
    this.player = null;
    this.revealed = new Set();
    this.cellPx = 40;

    this.timerHandle = null;
    this.animHandle = null;
    this.inputLocked = false;
    this._treasureMsgShown = false;

    this.subjectId = generateSubjectId();
    this.lastRecord = null; // 統計ページから結果画面へ戻れるように直近の結果を保持
  }

  init() {
    this.ui.showLabBadge(this.subjectId);

    document.getElementById("btn-start").addEventListener("click", () => this.startNewGame());
    document.getElementById("btn-howto").addEventListener("click", () => this.ui.showScreen("screen-howto"));
    document.getElementById("btn-howto-back").addEventListener("click", () => this.ui.showScreen("screen-title"));
    document.getElementById("btn-retry").addEventListener("click", () => this.startNewGame());
    document.getElementById("btn-title").addEventListener("click", () => {
      this.ui.hideLabBadge();
      this.ui.hideRec();
      this.ui.showScreen("screen-title");
    });
    document.getElementById("btn-stats").addEventListener("click", () => this.showStats());
    document.getElementById("btn-stats-back").addEventListener("click", () => this.ui.showScreen("screen-result"));
    document.getElementById("btn-stats-title").addEventListener("click", () => {
      this.ui.hideLabBadge();
      this.ui.hideRec();
      this.ui.showScreen("screen-title");
    });

    window.addEventListener("keydown", (e) => this._handleKey(e));
    document.querySelectorAll(".dpad-btn").forEach((btn) => {
      const fire = (ev) => { ev.preventDefault(); this.tryMove(btn.dataset.dir); };
      btn.addEventListener("click", fire);
      btn.addEventListener("touchstart", fire, { passive: false });
    });

    window.addEventListener("resize", () => this._resizeCanvases());
  }

  startNewGame() {
    this.ui.showLabBadge(this.subjectId);
    this.ui.setRecRecording();

    this.maze = new MazeGenerator(this.COLS, this.ROWS);
    this.player = new PlayerController(this.maze);
    this.revealed = new Set();
    this._revealCellAndNeighbors(0, 0);
    this.inputLocked = false;
    this._treasureMsgShown = false;

    this.ui.updateMission("宝箱を見つけよう");
    this.ui.setTreasureAcquired(false);
    this.ui.updateSteps(0);
    this.ui.updateTimer(0);

    this.ui.showScreen("screen-game");
    this._resizeCanvases();
    this.player.startClock();
    this._startTimer();
    this._renderAll();
    if (!this.animHandle) this._loop();
  }

  _resizeCanvases() {
    if (!this.maze) return;
    const dungeonCanvas = document.getElementById("dungeon-canvas");
    const wrap = dungeonCanvas.parentElement;
    const availW = wrap.clientWidth * 0.92;
    const availH = wrap.clientHeight * 0.92;
    const cellW = availW / this.maze.cols;
    const cellH = availH / this.maze.rows;
    this.cellPx = Math.max(18, Math.floor(Math.min(cellW, cellH)));
    dungeonCanvas.width = this.cellPx * this.maze.cols;
    dungeonCanvas.height = this.cellPx * this.maze.rows;
    this._renderAll();
  }

  _revealCellAndNeighbors(c, r) {
    this.revealed.add(cellKey(c, r));
    for (const n of this.maze.neighborsOf(c, r)) this.revealed.add(cellKey(n.c, n.r));
  }

  _handleKey(e) {
    const map = {
      ArrowUp: "up", w: "up", W: "up",
      ArrowDown: "down", s: "down", S: "down",
      ArrowLeft: "left", a: "left", A: "left",
      ArrowRight: "right", d: "right", D: "right",
    };
    const dir = map[e.key];
    if (!dir) return;
    if (!document.getElementById("screen-game").classList.contains("active")) return;
    e.preventDefault();
    this.tryMove(dir);
  }

  tryMove(dir) {
    if (this.inputLocked || !this.player || this.player.moving) return;
    const result = this.player.tryMove(dir);
    if (!result.moved) return;

    this.ui.updateSteps(this.player.totalSteps);

    if (result.treasureJustCollected) {
      this._treasureMsgShown = true;
      this.ui.setTreasureAcquired(true);
      this.ui.showTreasurePopup();
      this.ui.updateMission("ゴールを目指そう");
    }

    this._revealCellAndNeighbors(this.player.c, this.player.r);

    if (result.reachedGoal) {
      if (this.player.treasureCollected) {
        this._onGameClear();
      } else {
        this.ui.showFloatingMessage("まだ宝箱を見つけていない…！");
      }
    }
  }

  _startTimer() {
    this._stopTimer();
    this.timerHandle = setInterval(() => {
      this.ui.updateTimer(this.player.elapsedSeconds);
    }, 250);
  }
  _stopTimer() {
    if (this.timerHandle) clearInterval(this.timerHandle);
    this.timerHandle = null;
  }

  _loop() {
    this.player && this.player.updateAnimation();
    if (document.getElementById("screen-game").classList.contains("active")) this._renderAll();
    this.animHandle = requestAnimationFrame(() => this._loop());
  }

  _renderAll() {
    if (!this.maze || !this.player) return;
    const dungeonCanvas = document.getElementById("dungeon-canvas");
    Renderer.drawDungeon(dungeonCanvas.getContext("2d"), this.maze, this.revealed, this.player, this.cellPx);
    const minimapCanvas = document.getElementById("minimap-canvas");
    Renderer.drawMinimap(minimapCanvas.getContext("2d"), this.maze, this.revealed, this.player);
  }

  async _onGameClear() {
    this.inputLocked = true;
    this.player.stopClock();
    this._stopTimer();
    await this.ui.playAnalyzingSequence();
    this.ui.setRecStopped();
    await this._buildAndShowResult();
  }

  async _buildAndShowResult() {
    const analysis = Analyzer.analyze(this.player);

    // 保存・QR・画面表示すべてで使い回す「結果レコード」を1つにまとめる
    const record = {
      id: generateRecordId(),
      pid: this.subjectId,
      typeCode: analysis.typeCode,
      titleIndex: analysis.titleIndex,
      commentIndex: analysis.commentIndex,
      title: analysis.title,
      comment: analysis.comment,
      dfsScore: analysis.dfsScore,
      bfsScore: analysis.bfsScore,
      linearScore: analysis.linearScore,
      steps: analysis.stats.totalSteps,
      stepDiff: analysis.stats.stepDiff,
      explorationRate: analysis.stats.explorationRate,
      elapsedSeconds: analysis.stats.elapsedSeconds,
      timestamp: Date.now(),
    };
    this.lastRecord = record;

    // 統計ページ用にローカル保存（将来Firebase等に切り替える場合もここは変更不要）
    await this.storage.saveResult(record);

    this.resultRenderer.renderResult(record, this.maze, this.player);

    const cardUrl = QRManager.buildCardUrl(record);
    QRManager.renderInto(
      document.getElementById("qr-canvas-wrap"),
      document.getElementById("qr-fallback-url"),
      cardUrl
    );

    this.ui.showScreen("screen-result");
  }

  async showStats() {
    const stats = await this.storage.getAggregateStats();
    this.resultRenderer.renderStats(stats);
    this.ui.showScreen("screen-stats");
  }

  /** URLのクエリに診断カード情報が含まれていれば、カード画面を直接表示する */
  async tryShowCardFromUrl() {
    const cardData = QRManager.parseCardParams(location.search);
    if (!cardData) return false;

    if (cardData.idOnly) {
      // 軽量形式(id参照)の場合は、この端末に保存された記録から探す。
      // 別の端末（例：来場者のスマホ）では見つからないのが自然な挙動のため、
      // その場合はエラーで画面を壊さず、案内メッセージを表示する。
      const found = await this.storage.getResultById(cardData.id);
      if (found) {
        this.resultRenderer.renderCard({
          typeCode: found.typeCode,
          titleIndex: found.titleIndex,
          commentIndex: found.commentIndex,
          dfsScore: found.dfsScore,
          bfsScore: found.bfsScore,
          linearScore: found.linearScore,
          elapsedSeconds: found.elapsedSeconds,
          steps: found.steps,
          pid: found.pid,
        });
        this.ui.showScreen("screen-card");
        return true;
      }
      document.getElementById("card-title").textContent = "記録が見つかりませんでした";
      document.getElementById("card-comment").textContent =
        "この端末には診断データが保存されていません。QRコードを発行した端末でお試しください。";
      this.ui.showScreen("screen-card");
      return true;
    }

    this.resultRenderer.renderCard(cardData);
    this.ui.showScreen("screen-card");
    return true;
  }
}


/* ================================================================
   初期化処理
================================================================ */
window.addEventListener("DOMContentLoaded", async () => {
  const game = new GameManager();
  game.init();
  // QRコード経由でアクセスされた場合は診断カード画面を直接表示する
  const shownCard = await game.tryShowCardFromUrl();
  if (!shownCard) {
    game.ui.showScreen("screen-title");
  }
});
