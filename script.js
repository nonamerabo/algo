/* ================================================================
   Algorithm Research Lab - script.js
   ----------------------------------------------------------------
   【クラス構成（保守性向上のため責務ごとに分離しています）】
     MazeGenerator   : 迷路とマップギミック（ワープ・落とし穴等）の生成
     PlayerController: プレイヤーの位置・移動・探索ログ・ギミック状態の記録
     Analyzer        : 探索ログからDFS/BFS/線形探索らしさを診断（ルールベース）
     StorageManager  : 診断結果の保存（今はlocalStorage／将来Firebase等に差し替え可能）
     StatisticsManager: 保存された記録からの集計・ランキング・平均値の算出
     QRManager       : 診断カードURLの組み立て・QRコード生成/表示
     LogManager      : 研究所ログの表示演出（世界観演出のみ・ゲームに影響しない）
     UIManager       : 画面切り替え・HUD更新・各種演出などDOM操作全般
     ResultRenderer  : 診断結果画面／統計ページ／診断カードの描画
     GameManager     : 上記すべてを繋いでゲーム全体の流れを制御する司令塔

   SimpleQR（QRコードの符号化エンジン本体）と Renderer（キャンバス
   描画の共通関数集）は、上記クラスから利用される「低レベルの道具箱」
   として独立させています。
================================================================ */

"use strict";

// ブラウザが前回のスクロール位置を復元して、次の画面が下から始まるのを防ぐ
if ("scrollRestoration" in history) {
  history.scrollRestoration = "manual";
}

/* ================================================================
   共通ユーティリティ
================================================================ */
function randInt(max) {
  return Math.floor(Math.random() * max);
}
function pickRandom(arr) {
  return arr[randInt(arr.length)];
}
function clamp(v, min, max) {
  return Math.max(min, Math.min(max, v));
}
/** 4〜6桁のランダムな被験者IDを生成する */
function generateSubjectId() {
  const digits = 4 + randInt(3);
  let id = "";
  for (let i = 0; i < digits; i++) id += randInt(10);
  return id;
}
/** 統計保存用のユニークID（QRのURLにも載るため短く保つ） */
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
/** 配列をシャッフルして新しい配列を返す（Fisher-Yates） */
function shuffleArray(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = randInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}


/* ================================================================
   MazeGenerator
   ----------------------------------------------------------------
   再帰的バックトラッカー法で、全マスが1本の通路網でつながった
   「木構造の迷路」を生成する。木構造なので、スタート→宝箱→ゴールの
   本筋ルートは必ず一意に定まり、それ以外の道は必ず行き止まりになる。
   ⑩マップギミック（ワープ・落とし穴）は、
   すべて「本筋ルートから外れた行き止まり」にのみ配置することで、
   ギミックの有無にかかわらずゲームが必ずクリア可能であることを保証する。
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
    this.gimmicks = this._placeGimmicks();
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

  /**
   * ⑩マップギミックを配置する。
   * 本筋ルート（スタート→宝箱→ゴール）とは異なる「行き止まり」だけを
   * 候補にすることで、ギミックが無くても・使わなくても、
   * ゲームは必ずクリアできる状態を保つ。
   */
  _placeGimmicks() {
    const mainPath = this.shortestPath(this.start, this.goal).map((p) => cellKey(p.c, p.r));
    const usedKeys = new Set([
      cellKey(this.start.c, this.start.r),
      cellKey(this.goal.c, this.goal.r),
      cellKey(this.treasure.c, this.treasure.r),
      ...mainPath,
    ]);

    const candidates = [];
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const key = cellKey(c, r);
        if (this.isDeadEnd(c, r) && !usedKeys.has(key)) candidates.push({ c, r });
      }
    }
    const pool = shuffleArray(candidates);

    const takeOne = () => {
      while (pool.length > 0) {
        const cell = pool.pop();
        const key = cellKey(cell.c, cell.r);
        if (!usedKeys.has(key)) { usedKeys.add(key); return cell; }
      }
      return null; // 迷路が小さすぎて候補が足りない場合は諦める（安全側に倒す）
    };

    return {
      warpA: takeOne(),
      warpB: takeOne(),
      pitfall: takeOne(),
    };
  }

  /** 指定セルにギミックがあれば種類を返す（無ければnull） */
  gimmickTypeAt(c, r) {
    const g = this.gimmicks;
    if (g.warpA && g.warpA.c === c && g.warpA.r === r) return "warpA";
    if (g.warpB && g.warpB.c === c && g.warpB.r === r) return "warpB";
    if (g.pitfall && g.pitfall.c === c && g.pitfall.r === r) return "pitfall";
    return null;
  }

  /** ワープの対になる行き先を返す */
  warpDestination(which) {
    return which === "warpA" ? this.gimmicks.warpB : this.gimmicks.warpA;
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
   プレイヤーの位置管理・移動処理・探索ログの記録に加えて、
   ⑩マップギミック（ワープ・落とし穴）との
   やり取りの状態管理も担当する。
================================================================ */
class PlayerController {
  constructor(maze) {
    this.maze = maze;
    this.c = maze.start.c;
    this.r = maze.start.r;
    this.drawC = this.c;
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

    // ⑩ギミック関連の状態
    this.pitfallHits = 0;
    this.warpUsed = 0;
  }

  startClock() { this.startTime = performance.now(); }
  stopClock() { this.endTime = performance.now(); }

  /**
   * 方向キー入力を受けて移動を試みる。
   * @returns {{moved:boolean, reachedGoal:boolean, treasureJustCollected:boolean, message:?string}}
   */
  tryMove(dir) {
    const noop = { moved: false, reachedGoal: false, treasureJustCollected: false, message: null };
    if (this.moving) return noop;
    const DIR_MAP = {
      up: { key: "N", dc: 0, dr: -1 },
      down: { key: "S", dc: 0, dr: 1 },
      left: { key: "W", dc: -1, dr: 0 },
      right: { key: "E", dc: 1, dr: 0 },
    };
    const d = DIR_MAP[dir];
    if (!d) return noop;

    const cell = this.maze.cellAt(this.c, this.r);
    if (cell[d.key]) return noop; // 壁がある

    const from = { c: this.c, r: this.r };
    const to = { c: this.c + d.dc, r: this.r + d.dr };

    const gimmickType = this.maze.gimmickTypeAt(to.c, to.r);

    this._recordMove(from, to);
    this.c = to.c;
    this.r = to.r;
    this.moving = true;

    const treasureJustCollected =
      this.treasureCollected && this.treasureStepIndex === this.path.length - 1;

    let message = null;
    if (gimmickType === "pitfall") {
      this.pitfallHits++;
      message = "落とし穴に落ちた…スタート地点に戻される！";
      this._teleportTo(this.maze.start);
    } else if (gimmickType === "warpA" || gimmickType === "warpB") {
      this.warpUsed++;
      message = "ワープした！";
      this._teleportTo(this.maze.warpDestination(gimmickType));
    }

    const reachedGoal = this.c === this.maze.goal.c && this.r === this.maze.goal.r;
    return { moved: true, reachedGoal, treasureJustCollected, message };
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

  /** ワープ・落とし穴用：自発的な移動ではない「瞬間移動」の記録（簡易版） */
  _teleportTo(dest) {
    if (!dest) return;
    const key = cellKey(dest.c, dest.r);
    if (this.visitCounts.has(key)) {
      this.revisitCount++;
      this.visitCounts.set(key, this.visitCounts.get(key) + 1);
    } else {
      this.visitCounts.set(key, 1);
    }
    this.path.push({ ...dest });
    this.c = dest.c;
    this.r = dest.r;
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
   ⑩マップギミックの利用状況（危険回避・冒険心）も加味して、
   「危険回避タイプ」「型破りな挑戦者」といった特別な診断も行います。
   ⑦診断コメントは、初心者向け／研究者風／AI口調／ユーモア／RPG風の
   5つのトーンを組み合わせ、各タイプ20種類以上を用意しています。
================================================================ */
const Analyzer = {
  TITLE_POOL: {
    D: ["探究者", "冒険家", "未知への挑戦者"],
    B: ["最短マスター", "効率の探検家", "先読みの達人"],
    L: ["慎重派", "丁寧な観察者", "一歩ずつの職人"],
    X: ["アルゴリズム博士", "万能型研究者"],
    R: ["危険回避タイプ", "慎重派の生存者"],
    A: ["型破りな挑戦者", "冒険家（型破り型）"],
  },

  // ---- DFSタイプのコメント（初心者/研究者/AI口調/ユーモア/RPG風 × 各5 = 25） ----
  COMMENT_POOL_D: [
    // 初心者向け
    "気になる道はとことん進んじゃうタイプだね！",
    "行き止まりを見ても『とりあえず行ってみよう』と思うタイプみたい。",
    "新しい道を見つけると、つい奥まで確かめたくなるタイプかも。",
    "一つの道を最後まで確かめてから次に進む、まっすぐな探検スタイルだよ。",
    "『とりあえずやってみる』を体現するような動き方でした。",
    // 研究者風
    "観測データより、経路選択において深さ優先の傾向が強く見られました。",
    "未探索領域への遷移が、探索済み領域への回帰よりも高頻度で確認されています。",
    "行動パターンは、スタックベースの探索アルゴリズムに酷似しています。",
    "被験者は分岐において常に「最も深い」選択肢を優先する傾向が見られました。",
    "本行動データは、深さ優先探索(DFS)モデルとの高い一致率を示しています。",
    // AI口調
    "行動解析完了。パターン分類：探索優先型。",
    "……あなたの思考回路、面白いですね。奥へ、奥へ。",
    "深度探索モード確認。これはこれで一つの正解です。",
    "被験者の意思決定に一定の法則性を検出しました：『進めるなら進む』。",
    "興味深い。あなたは迷いなく、闇の奥へ向かっていく。",
    // ユーモア
    "行き止まりにぶつかっても『来た道は戻らない』主義のようです。",
    "宝箱よりも先に、迷路の隅々が気になって仕方がない性格のようです。",
    "『まだ引き返すには早い』が口癖になっていそうなタイプ。",
    "迷路の隅っこまで制覇しないと気が済まない、そんな探究心の持ち主。",
    "帰り道のことは、また今度考えるタイプですね。",
    // RPG風
    "『この先に何があるか確かめずにはいられない』――そんな冒険者気質。",
    "未知のダンジョンほど燃えるタイプの勇者だ。",
    "仲間より先に、一人で奥へ進んでしまう先陣切りタイプ。",
    "『行けるところまで行く』——それがあなたの流儀。",
    "伝説の勇者も、きっと同じように奥へ奥へと突き進んだのだろう。",
    // 追加（初心者/研究者/AI口調/ユーモア/RPG風）
    "とにかく『この先どうなってるんだろう』が気になって仕方ない性格みたい。",
    "被験者の移動経路は、深さ優先探索(DFS)の理論モデルと非常に近い形状を描いています。",
    "解析完了。あなたの思考は『まず奥まで、話はそれから』のようです。",
    "行き止まりコレクターの才能があるかもしれません。",
    "『引き返すのは全部確かめてから』——生粋の一本道タイプの冒険者。",
  ],

  // ---- BFSタイプのコメント（25） ----
  COMMENT_POOL_B: [
    "近くから順番に、しっかり確認していくタイプだね！",
    "遠回りが少なくて、効率よくゴールへ向かえるタイプみたい。",
    "『まずは周りから』を大事にする、バランス型の探検スタイル。",
    "無駄な後戻りが少なくて、まっすぐゴールに向かえていたよ。",
    "見晴らしの良い進み方で、迷わずゴールできていたね。",
    "観測データより、最短経路との乖離が極めて小さいことが確認されました。",
    "移動パターンは幅優先探索(BFS)モデルと高い一致率を示しています。",
    "被験者は近傍領域を優先的に確認したのち、次の階層へ移行する傾向が見られました。",
    "行動全体を通して、効率性を重視した意思決定が観測されています。",
    "探索コストと到達コストのバランスが非常に良好です。",
    "行動解析完了。パターン分類：効率優先型。",
    "無駄がない。とても『合理的』な思考回路です。",
    "最短経路モデルとの一致を確認。これは……優秀です。",
    "被験者の意思決定に法則性を検出：『近い方から確かめる』。",
    "興味深い。あなたは迷わず、最適な道を選び続けている。",
    "『急がば回れ』ではなく『急がば最短』を地で行くタイプ。",
    "宝箱もゴールも、最短距離で回収する効率派のようです。",
    "遠回りしている自分を許せないタイプかもしれません。",
    "迷路すら『最適化』しようとする、生粋の効率主義者。",
    "無駄な一歩を歩くくらいなら、少し立ち止まって考えるタイプ。",
    "『最短でゴールへ辿り着く』——そんな戦略家タイプの冒険者。",
    "地図を読むのが得意な、パーティの道案内役タイプ。",
    "遠回りは嫌い。最短距離で目的を果たすタイプの英雄。",
    "『無駄な回り道は避ける』——効率を重んじる冒険者気質。",
    "最短ルートを見抜く目を持った、まさにナビゲータータイプ。",
    // 追加（初心者/研究者/AI口調/ユーモア/RPG風）
    "近くをぱぱっと確認してから動く、テンポの良い探し方だったよ。",
    "被験者の移動経路は、幅優先探索(BFS)の理論モデルに極めて近い形状を描いています。",
    "解析完了。あなたの思考は『広く見てから、一番近道を選ぶ』のようです。",
    "遠回りしている人を見ると、つい教えたくなるタイプかもしれません。",
    "『最短ルートこそ我が道』——効率を愛する戦略家タイプの冒険者。",
  ],

  // ---- 線形探索タイプのコメント（25） ----
  COMMENT_POOL_L: [
    "一つずつ順番に、丁寧に確認していくタイプだね！",
    "焦らずじっくり進む、慎重な探検スタイルみたい。",
    "同じような手順で、コツコツ確かめていくタイプだよ。",
    "『まず手前から』を大事にする、堅実な進み方だね。",
    "見落としがないように、順番に確認していくタイプみたい。",
    "観測データより、分岐選択の順序に高い規則性が確認されました。",
    "被験者は毎回ほぼ同じ優先順位で選択肢を確認する傾向にあります。",
    "行動パターンは線形探索(Linear Search)モデルに近い挙動を示しています。",
    "移動の再現性が高く、手順の一貫性が観測されています。",
    "被験者は網羅性を重視し、確実性の高い探索を行っています。",
    "行動解析完了。パターン分類：規則優先型。",
    "規則正しい。とても『予測しやすい』思考回路です。",
    "手順の一貫性を確認。これは……堅実です。",
    "被験者の意思決定に法則性を検出：『順番通りに確かめる』。",
    "興味深い。あなたは一貫した手順で、着実に前進している。",
    "『抜け道』より『正攻法』を選びがちなタイプ。",
    "とりあえず順番に全部見ないと気が済まない性格かも。",
    "近道を見つけても、律儀に手順を踏んでしまうタイプ。",
    "『まあ一応、確認だけしておくか』が口癖になっていそう。",
    "せっかちとは無縁の、じっくり型の探検家。",
    "『一つずつ確実に』——堅実な戦術を好む冒険者タイプ。",
    "抜かりのない準備を大切にする、職人肌の冒険者。",
    "運任せよりも手順を信じる、堅実派の戦略家。",
    "『慌てず、騒がず、順番に』——そんな渋いスタイルの旅人。",
    "確実な一歩を積み重ねる、縁の下の力持ちタイプ。",
    // 追加（初心者/研究者/AI口調/ユーモア/RPG風）
    "見落としが一番怖い、というタイプの慎重な性格みたい。",
    "被験者の移動パターンは、線形探索(Linear Search)の理論モデルと高い一致率を示しています。",
    "解析完了。あなたの思考は『飛ばさず、順番に、確実に』のようです。",
    "ショートカットを見つけても、律儀に確認作業を続けるタイプかもしれません。",
    "『一歩ずつ、抜かりなく』——堅実さを何より重んじる旅人タイプ。",
  ],

  // ---- 特別タイプのコメント ----
  COMMENT_POOL_X: [
    "DFS・BFS・線形探索、すべての思考を兼ね備えた稀有なタイプです。",
    "状況に応じて探索スタイルを使い分ける、柔軟な思考の持ち主のようです。",
    "一つの型に収まらない、まさに『万能型』の探索者です。",
    "研究員も驚きの、バランスの取れた思考パターンを確認しました。",
    "どのアルゴリズムにも偏らない、稀に見るオールラウンダーです。",
    "被験者データベースの中でも、極めて珍しいタイプに分類されました。",
    "深く進み、広く見て、丁寧に確かめる——すべてを兼ね備えています。",
    "これぞ『アルゴリズム博士』と呼ぶにふさわしい探索スタイルです。",
  ],
  COMMENT_POOL_R: [
    "危険な仕掛けを一度も踏まず、安全第一で進んでいました。",
    "リスクを避けながらも、隠された部屋までしっかり見つけ出しています。",
    "『石橋を叩いて渡る』を体現するような、堅実な立ち回りでした。",
    "落とし穴の気配を察知しているかのような、慎重な足取りでした。",
    "安全に、しかし手は抜かない。バランス感覚に優れた探索者です。",
    "危険を避けながらも成果はしっかり持ち帰る、頼れるタイプです。",
    "研究員一同、その慎重さに感心しています。",
    "危機管理能力の高さが、行動データからうかがえます。",
  ],
  COMMENT_POOL_A: [
    "危険を恐れず、仕掛けにも果敢に飛び込んでいくタイプです。",
    "落とし穴もワープも、まずは踏んでみるタイプのようです。",
    "予測不能な行動が、かえって新しい発見につながっていました。",
    "『まずやってみる』精神が随所に表れています。",
    "ハプニングすら楽しんでいるような、大胆な探索スタイルでした。",
    "型にはまらない自由な発想の持ち主のようです。",
    "リスクを取ってでも新しい体験を求める、冒険者気質です。",
    "研究員も予測できなかった、ユニークな行動データでした。",
  ],

  /** アルゴリズムの解説文（⑦小学生でも分かる説明＋図解イメージ＋メリデメ＋実例） */
  ALGORITHM_INFO: {
    D: {
      name: "DFS（深さ優先探索）",
      emoji: "🌲",
      text: "一本道を最後まで進み、行き止まりまで行ってから戻る探し方です。迷路で「とりあえず最後まで行ってみよう！」と考える人に近いアルゴリズムです。",
      scenario: "枝分かれした道を、1つ選んだらそのまま奥まで突き進み、行き止まったら1つ手前に戻ってまた次の道へ――を繰り返す場面で使われます。",
      merit: "使うメモリ（覚えておく量）が少なくて済み、仕組みがシンプルです。迷路やパズルの「解けるか解けないか」を調べるのが得意です。",
      demerit: "運が悪いと、遠回りな道ばかり選んでしまい、ゴールまで時間がかかることがあります。最短ルートを見つけるのは苦手です。",
      example: "迷路の自動生成・数独やパズルの解法探し・将棋やオセロの手を読むプログラムなどで使われています。",
    },
    B: {
      name: "BFS（幅優先探索）",
      emoji: "🌊",
      text: "近くから順番に広く探していく方法です。遠回りを減らし、最短ルートを見つけることが得意です。",
      scenario: "今いる場所から1歩で行ける場所を全部確認し、それから2歩で行ける場所……というように、輪を広げるように探す場面で使われます。",
      merit: "一番少ない歩数でゴールにたどり着く「最短ルート」を必ず見つけられます。近道を見逃しません。",
      demerit: "一度に覚えておく場所の数が多くなりやすく、DFSに比べてメモリ（覚えておく量）を多く使います。",
      example: "カーナビの最短経路探索・SNSの「友達の友達」をたどる機能・路線検索アプリなどで使われています。",
    },
    L: {
      name: "線形探索",
      emoji: "📋",
      text: "最初から順番に一つずつ確認していく方法です。確実ですが、データが多いと時間がかかることがあります。",
      scenario: "リストや名簿を先頭から1件ずつ順番にチェックして、探しているものを見つける場面で使われます。",
      merit: "仕組みがとても分かりやすく、データが並んでいなくても（順番がバラバラでも）確実に見つけ出せます。",
      demerit: "データの数が多くなるほど、確認する回数も増えて時間がかかります。効率という点では他の方法に劣ります。",
      example: "電話帳から名前を1件ずつ探す・忘れ物を1つずつ確認する・簡単なリストの検索処理などで使われています。",
    },
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

    // ⑩ギミックの利用状況を軽く加味する（危険を厭わない=DFS寄り、慎重=線形寄り）
    if (player.pitfallHits > 0) dfsScore += 6;
    if (player.pitfallHits > 0) bfsScore -= 3 * player.pitfallHits;

    dfsScore = Math.round(clamp(dfsScore, 0, 100));
    bfsScore = Math.round(clamp(bfsScore, 0, 100));
    linearScore = Math.round(clamp(linearScore, 0, 100));

    const scores = { D: dfsScore, B: bfsScore, L: linearScore };
    const dominant = Object.keys(scores).reduce((a, b) => (scores[a] >= scores[b] ? a : b));

    let typeCode = dominant;
    if (dfsScore >= 65 && bfsScore >= 65 && linearScore >= 65) {
      typeCode = "X"; // 全部高水準ならアルゴリズム博士
    } else if (player.pitfallHits === 0 && Math.abs(player.stepDiff) <= idealSteps * 0.15) {
      typeCode = "R"; // 危険回避タイプ：罠を踏まず、効率も良い
    } else if (player.pitfallHits >= 1 || player.warpUsed >= 1) {
      typeCode = "A"; // 型破りな挑戦者：危険な仕掛けに突っ込んだ・ワープを使った
    }

    const commentPool = this._commentPoolFor(typeCode);
    const titleIndex = randInt(this.TITLE_POOL[typeCode].length);
    const commentIndex = randInt(commentPool.length);

    // ⑥「なぜこのタイプと診断されたのか」の根拠（プレイ内容ベース）
    const reasoning = this._buildReasoning(typeCode, {
      deadEndRatio, unexploredRatio, revisitRatio, diffRatio, systematicRatio,
      pitfallHits: player.pitfallHits, warpUsed: player.warpUsed,
    });

    return {
      dfsScore,
      bfsScore,
      linearScore,
      typeCode,
      titleIndex,
      commentIndex,
      title: this.TITLE_POOL[typeCode][titleIndex],
      comment: commentPool[commentIndex],
      reasoning,
      stats: {
        totalSteps: player.totalSteps,
        idealSteps,
        stepDiff: player.stepDiff,
        explorationRate: Math.round(explorationRate),
        elapsedSeconds: Math.round(player.elapsedSeconds),
      },
      gimmicks: {
        pitfallHits: player.pitfallHits,
        warpUsed: player.warpUsed,
      },
    };
  },

  _commentPoolFor(typeCode) {
    return {
      D: this.COMMENT_POOL_D, B: this.COMMENT_POOL_B, L: this.COMMENT_POOL_L,
      X: this.COMMENT_POOL_X, R: this.COMMENT_POOL_R, A: this.COMMENT_POOL_A,
    }[typeCode] || this.COMMENT_POOL_X;
  },

  _buildReasoning(typeCode, m) {
    const reasons = [];
    if (typeCode === "D" || typeCode === "X") {
      if (m.deadEndRatio > 0.35) reasons.push("行き止まりまで進む割合が高かった");
      if (m.unexploredRatio > 0.55) reasons.push("常に新しい道を優先して選んでいた");
      if (m.revisitRatio < 0.15) reasons.push("探索済みの場所へ戻る回数が少なかった");
    }
    if (typeCode === "B" || typeCode === "X") {
      if (m.diffRatio < 0.2) reasons.push("最短ルートとの差が少なかった");
      if (m.revisitRatio < 0.15) reasons.push("無駄な後戻りが少なかった");
    }
    if (typeCode === "L" || typeCode === "X") {
      if (m.systematicRatio > 0.5) reasons.push("分岐でいつも同じ順番に選択肢を確認していた");
    }
    if (typeCode === "R") {
      reasons.push("危険な仕掛け（落とし穴）に一度も引っかからなかった");
    }
    if (typeCode === "A") {
      if (m.pitfallHits > 0) reasons.push("落とし穴に落ちてもなお、探索をやめなかった");
      if (m.warpUsed > 0) reasons.push("ワープなど未知の仕掛けを積極的に利用した");
    }
    if (reasons.length === 0) reasons.push("全体的にバランスの取れた探索行動だった");
    return reasons;
  },

  /** typeCode + variant番号から称号・コメントを復元する（QRカード表示用） */
  reconstruct(typeCode, titleIndex, commentIndex) {
    const titles = this.TITLE_POOL[typeCode] || this.TITLE_POOL.X;
    const comments = this._commentPoolFor(typeCode);
    return {
      title: titles[titleIndex % titles.length] || titles[0],
      comment: comments[commentIndex % comments.length] || comments[0],
    };
  },
};


/* ================================================================
   StorageManager
   ----------------------------------------------------------------
   診断結果の保存（CRUD）だけを担当するクラス。集計・ランキングの
   計算は StatisticsManager 側の責務として分離している。
   今はブラウザのlocalStorageに保存しているが、メソッドはすべて
   async にしてあるため、将来Firebase等のオンラインDBに差し替える
   場合も、このクラスの中身だけを書き換えれば他のコードには
   影響しない設計になっている。
================================================================ */
class StorageManager {
  constructor() {
    this.storageKey = "algo_lab_results_v1";
    this.bootFlagKey = "algo_lab_boot_seen_v1";
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
      console.warn("localStorageが利用できないため、統計は保存されません。", e);
      return false;
    }
  }

  /** 1件の診断結果を保存する（過去の履歴は書き換えない・追記のみ） */
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

  /** ②SYSTEM BOOT演出を既に見たことがあるか */
  hasSeenBoot() {
    if (!this.available) return false;
    try {
      return localStorage.getItem(this.bootFlagKey) === "1";
    } catch (e) {
      return false;
    }
  }
  markBootSeen() {
    if (!this.available) return;
    try {
      localStorage.setItem(this.bootFlagKey, "1");
    } catch (e) { /* 保存できなくても致命的ではないので無視する */ }
  }

  /** 設定画面からの「履歴をリセットする」操作で使用する */
  async clearAllResults() {
    if (!this.available) return false;
    try {
      localStorage.removeItem(this.storageKey);
      return true;
    } catch (e) {
      console.warn("履歴のリセットに失敗しました。", e);
      return false;
    }
  }
}


/* ================================================================
   StatisticsManager
   ----------------------------------------------------------------
   StorageManagerが保持する記録から、集計値・ランキング・平均値を
   計算する専門クラス。StorageManagerを差し替えるだけで、この
   クラスのロジックはそのままオンラインDB集計にも転用できる。
================================================================ */
class StatisticsManager {
  constructor(storageManager) {
    this.storage = storageManager;
  }

  /** ④みんなの履歴ページ向けの集計一式 */
  async getAggregateStats() {
    const all = await this.storage.getAllResults();
    if (all.length === 0) {
      return {
        totalPlayers: 0,
        avgTime: 0,
        avgSteps: 0,
        typeRatio: { D: 0, B: 0, L: 0, X: 0, R: 0, A: 0 },
        titleRanking: [],
        fastestRanking: [],
        explorationRanking: [],
        recent: [],
      };
    }
    const totalPlayers = all.length;
    const avgTime = all.reduce((s, r) => s + r.elapsedSeconds, 0) / totalPlayers;
    const avgSteps = all.reduce((s, r) => s + r.steps, 0) / totalPlayers;

    const typeCounts = { D: 0, B: 0, L: 0, X: 0, R: 0, A: 0 };
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
    const recent = [...all].sort((a, b) => b.timestamp - a.timestamp).slice(0, 20);

    return { totalPlayers, avgTime, avgSteps, typeRatio, titleRanking, fastestRanking, explorationRanking, recent };
  }

  /** ⑤診断画面で「みんなの平均」と比較するための平均スコア */
  async getAverageScores() {
    const all = await this.storage.getAllResults();
    if (all.length === 0) return null; // まだ誰も遊んでいなければ比較できない
    const n = all.length;
    return {
      avgDfs: all.reduce((s, r) => s + r.dfsScore, 0) / n,
      avgBfs: all.reduce((s, r) => s + r.bfsScore, 0) / n,
      avgLinear: all.reduce((s, r) => s + r.linearScore, 0) / n,
      sampleSize: n,
    };
  }
}


/* ================================================================
   SettingsManager
   ----------------------------------------------------------------
   ④設定画面で扱う「端末ごとの表示設定」を管理するクラス。
   localStorageに保存し、次回アクセス時も設定を引き継ぐ。
================================================================ */
class SettingsManager {
  constructor() {
    this.key = "algo_lab_settings_v1";
    this.defaults = { reduceMotion: false };
    this.current = this._load();
  }

  _load() {
    try {
      const raw = localStorage.getItem(this.key);
      return raw ? { ...this.defaults, ...JSON.parse(raw) } : { ...this.defaults };
    } catch (e) {
      return { ...this.defaults };
    }
  }
  _save() {
    try {
      localStorage.setItem(this.key, JSON.stringify(this.current));
    } catch (e) { /* 保存できなくても致命的ではないので無視する */ }
  }

  get(key) { return this.current[key]; }
  set(key, value) {
    this.current[key] = value;
    this._save();
  }
  toggle(key) {
    this.set(key, !this.current[key]);
    return this.current[key];
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
   容量(約108バイト)を超える場合は自動でURLを短縮し、それでも
   収まらない場合はQR化を諦めてテキストリンクを表示することで、
   「読み取れるのに何も表示されない」壊れたQRを絶対に作らない。
================================================================ */
const QRManager = {
  QR_SAFE_BYTE_LIMIT: 100,

  _buildBaseUrl() {
    let base = location.origin + location.pathname;
    if (base.endsWith("/index.html")) base = base.slice(0, -"index.html".length);
    return base;
  },

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
    if (new TextEncoder().encode(fullUrl).length <= this.QR_SAFE_BYTE_LIMIT) return fullUrl;

    if (record.id) {
      const shortParams = new URLSearchParams();
      shortParams.set("id", record.id);
      const shortUrl = `${base}?${shortParams.toString()}`;
      if (new TextEncoder().encode(shortUrl).length <= this.QR_SAFE_BYTE_LIMIT) return shortUrl;
    }
    return fullUrl;
  },

  parseCardParams(search) {
    const params = new URLSearchParams(search);
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
    if (params.get("id")) return { idOnly: true, id: params.get("id") };
    return null;
  },

  renderInto(wrapEl, fallbackEl, url) {
    wrapEl.innerHTML = "";
    fallbackEl.classList.add("hidden");

    const byteLength = new TextEncoder().encode(url).length;
    if (byteLength > this.QR_SAFE_BYTE_LIMIT) {
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
      console.error("QR生成に失敗しました:", err);
      fallbackEl.textContent = url;
      fallbackEl.classList.remove("hidden");
    }
  },
};


/* ================================================================
   LogManager
   ----------------------------------------------------------------
   ①研究所ログのティッカー表示と、⑫ランダムなポップアップ演出を
   担当する。世界観を盛り上げるための純粋な演出であり、ゲームの
   判定やスコアには一切影響しない。
================================================================ */
class LogManager {
  constructor() {
    this.tickerLines = [
      "Collecting Data...", "Analyzing Behavior...", "Behavior Recording...",
      "Unknown Pattern Detected...", "Branch Decision Logged...", "Exploration Data Saved...",
      "Tracking Movement...", "Synchronizing Logs...", "Cross-referencing Patterns...",
      "Behavior Model Updating...", "Subject Response Nominal...", "Path Deviation Logged...",
      "Decision Tree Expanding...", "Cognitive Pattern Sampling...", "Node Traversal Recorded...",
      "Signal Noise: Low...", "Memory Buffer Stable...", "Awaiting Next Action...",
      "Anomaly Scan: Clear...", "Data Stream Stable...",
      "Thinking Pattern Updated...", "Memory Recording...", "AI Learning...",
      "Behavior Classification...", "Node Analysis...", "Data Synchronizing...",
    ];
    this.popupLines = [
      "行動記録更新", "探索率解析中", "未知パターン検出", "思考モデル更新",
      "AI学習完了", "データ同期中", "研究ログ保存", "分岐選択を記録",
      "観測データ更新中", "被験者行動を記録中", "Memory Saved", "Behavior Matched",
    ];
    this.tickerHandle = null;
    this.popupTimeoutHandle = null;
  }

  startTicker(elementId, minMs = 2500, maxMs = 4000) {
    this.stopTicker();
    const el = document.getElementById(elementId);
    if (!el) return;
    const tick = () => {
      el.textContent = pickRandom(this.tickerLines);
      const delay = minMs + Math.random() * (maxMs - minMs);
      this.tickerHandle = setTimeout(tick, delay);
    };
    tick();
  }
  stopTicker() {
    if (this.tickerHandle) clearTimeout(this.tickerHandle);
    this.tickerHandle = null;
  }

  startPopups(elementId, minMs = 9000, maxMs = 17000) {
    this.stopPopups();
    const el = document.getElementById(elementId);
    if (!el) return;
    const schedule = () => {
      const delay = minMs + Math.random() * (maxMs - minMs);
      this.popupTimeoutHandle = setTimeout(() => {
        el.textContent = pickRandom(this.popupLines);
        el.classList.remove("hidden");
        el.classList.remove("show");
        void el.offsetWidth;
        el.classList.add("show");
        setTimeout(() => { el.classList.add("hidden"); el.classList.remove("show"); }, 2400);
        schedule();
      }, delay);
    };
    schedule();
  }
  stopPopups() {
    if (this.popupTimeoutHandle) clearTimeout(this.popupTimeoutHandle);
    this.popupTimeoutHandle = null;
  }

  stop() {
    this.stopTicker();
    this.stopPopups();
  }
}


/* ================================================================
   Renderer（キャンバス描画の共通処理）
================================================================ */
const Renderer = {
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

        // 宝箱：8bit RPG風。取得前は閉じた宝箱、取得後は開いた宝箱にする
        if (c === maze.treasure.c && r === maze.treasure.r) {
          Renderer._drawTreasure(ctx, x, y, cellPx, player.treasureCollected);
        }
        // ゴール：チェック柄のRPG風フラッグ
        if (c === maze.goal.c && r === maze.goal.r) {
          Renderer._drawGoalFlag(ctx, x, y, cellPx);
        }

        // ⑩マップギミックの描画
        const gimmick = maze.gimmickTypeAt(c, r);
        if (gimmick === "warpA" || gimmick === "warpB") Renderer._drawWarp(ctx, x, y, cellPx);
        if (gimmick === "pitfall") Renderer._drawPitfall(ctx, x, y, cellPx);
      }
    }

    const px = player.drawC * cellPx;
    const py = player.drawR * cellPx;
    ctx.fillStyle = "#4deeea";
    ctx.fillRect(px + cellPx * 0.22, py + cellPx * 0.18, cellPx * 0.56, cellPx * 0.64);
    ctx.fillStyle = "#0a0e17";
    ctx.fillRect(px + cellPx * 0.34, py + cellPx * 0.36, cellPx * 0.1, cellPx * 0.1);
    ctx.fillRect(px + cellPx * 0.56, py + cellPx * 0.36, cellPx * 0.1, cellPx * 0.1);

    if (player.treasureCollected) {
      ctx.fillStyle = "#ffce54";
      ctx.fillRect(px + cellPx * 0.36, py - cellPx * 0.06, cellPx * 0.28, cellPx * 0.16);
    }
  },

  _drawTreasure(ctx, x, y, cellPx, opened = false) {
    const u = cellPx / 16;
    const px = (n) => Math.round(n * u);
    const ox = x + px(3);
    const oy = y + px(4);
    const R = (gx, gy, gw, gh, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(ox + px(gx), oy + px(gy), px(gw), px(gh));
    };

    ctx.save();
    ctx.imageSmoothingEnabled = false;

    // シンプルでポップな8bit宝箱。小さくても「宝箱」と分かるよう形を優先する。
    ctx.shadowColor = opened ? "rgba(77,238,234,0.28)" : "rgba(255,206,84,0.55)";
    ctx.shadowBlur = Math.max(4, cellPx * 0.14);
    ctx.fillStyle = opened ? "rgba(77,238,234,0.08)" : "rgba(255,206,84,0.10)";
    ctx.fillRect(x + px(4), y + px(12), px(8), px(2));
    ctx.shadowBlur = 0;

    if (!opened) {
      // closed cute chest: rounded lid, gold frame, center keyhole
      R(2, 4, 10, 1, "#3a1d10");
      R(1, 5, 12, 3, "#8b4a24");
      R(2, 5, 10, 1, "#c96f31");
      R(2, 7, 10, 1, "#5a2e19");
      R(1, 8, 12, 4, "#6f3a1d");
      R(2, 8, 10, 1, "#a75a2a");
      R(2, 11, 10, 1, "#3a1d10");

      // gold trim kept chunky and readable
      R(1, 8, 12, 1, "#ffcf4a");
      R(1, 5, 2, 7, "#e6a63a");
      R(11, 5, 2, 7, "#e6a63a");
      R(6, 5, 2, 7, "#ffcf4a");
      R(2, 5, 1, 1, "#fff1a8");
      R(11, 5, 1, 1, "#fff1a8");

      // lock plate + keyhole
      R(5, 8, 4, 3, "#ffcf4a");
      R(6, 9, 2, 2, "#05070d");
      R(7, 10, 1, 1, "#05070d");

      // tiny sparkle: attractive but not too noisy
      R(13, 2, 1, 1, "#fff1a8");
      R(12, 3, 3, 1, "#ffcf4a");
      R(13, 4, 1, 1, "#fff1a8");
      R(0, 3, 1, 1, "#fff1a8");
    } else {
      // opened chest: lid is clearly open, box remains intact and empty
      R(2, 1, 10, 1, "#3a1d10");
      R(1, 2, 12, 3, "#8b4a24");
      R(2, 2, 10, 1, "#c96f31");
      R(1, 5, 12, 1, "#ffcf4a");

      R(1, 8, 12, 4, "#6f3a1d");
      R(2, 8, 10, 1, "#a75a2a");
      R(2, 11, 10, 1, "#3a1d10");
      R(1, 8, 12, 1, "#ffcf4a");
      R(1, 8, 2, 4, "#e6a63a");
      R(11, 8, 2, 4, "#e6a63a");
      R(6, 8, 2, 4, "#ffcf4a");

      // empty dark interior, not a broken box
      R(3, 6, 8, 2, "#130a0b");
      R(4, 7, 6, 1, "#28120e");
      R(5, 9, 4, 2, "#26120c");

      // small completion mark, kept pixel-art simple
      R(12, 2, 1, 2, "#72ff8a");
      R(13, 3, 2, 1, "#72ff8a");
    }
    ctx.restore();
  },

  _drawGoalFlag(ctx, x, y, cellPx) {
    const poleX = x + cellPx * 0.32;
    const poleTopY = y + cellPx * 0.16;
    const poleBottomY = y + cellPx * 0.86;
    ctx.strokeStyle = "#d8d2c2";
    ctx.lineWidth = Math.max(2, cellPx * 0.06);
    ctx.beginPath();
    ctx.moveTo(poleX, poleTopY);
    ctx.lineTo(poleX, poleBottomY);
    ctx.stroke();
    const flagW = cellPx * 0.4;
    const flagH = cellPx * 0.28;
    const half = flagH / 2;
    const halfW = flagW / 2;
    ctx.fillStyle = "#4deeea";
    ctx.fillRect(poleX, poleTopY, flagW, flagH);
    ctx.fillStyle = "#0a0e17";
    ctx.fillRect(poleX, poleTopY, halfW, half);
    ctx.fillRect(poleX + halfW, poleTopY + half, halfW, half);
    ctx.fillStyle = "#26314f";
    ctx.fillRect(poleX - cellPx * 0.08, poleBottomY - cellPx * 0.03, cellPx * 0.24, cellPx * 0.06);
  },

  _drawWarp(ctx, x, y, cellPx) {
    const u = cellPx / 16;
    const px = (n) => Math.round(n * u);
    const R = (gx, gy, gw, gh, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(x + px(gx), y + px(gy), px(gw), px(gh));
    };

    ctx.save();
    ctx.imageSmoothingEnabled = false;

    // AI研究所の小型転送装置：紫シアンの渦＋簡素な台座
    ctx.shadowColor = "rgba(77,238,234,0.78)";
    ctx.shadowBlur = Math.max(5, cellPx * 0.18);
    R(4, 12, 8, 2, "rgba(77,238,234,0.18)");
    ctx.shadowBlur = 0;

    // base pad
    R(4, 11, 8, 2, "#3b4657");
    R(5, 10, 6, 1, "#7b8a9d");
    R(6, 12, 1, 1, "#4deeea");
    R(10, 12, 1, 1, "#4deeea");
    R(4, 13, 8, 1, "#1b2333");

    // pop 8bit portal ring
    R(6, 2, 4, 1, "#b991ff");
    R(4, 3, 2, 2, "#8a56ff");
    R(10, 3, 2, 2, "#8a56ff");
    R(3, 5, 2, 4, "#6a3cff");
    R(11, 5, 2, 4, "#6a3cff");
    R(4, 9, 2, 2, "#8a56ff");
    R(10, 9, 2, 2, "#8a56ff");
    R(6, 11, 4, 1, "#b991ff");

    // inner electronic swirl
    R(6, 4, 4, 1, "#e4d4ff");
    R(5, 5, 2, 1, "#b991ff");
    R(8, 5, 3, 1, "#4deeea");
    R(9, 6, 2, 1, "#b991ff");
    R(6, 7, 4, 1, "#4deeea");
    R(5, 8, 2, 1, "#b991ff");
    R(7, 9, 4, 1, "#e4d4ff");

    // few pixels of digital sparkle
    R(2, 4, 1, 1, "#bfffff");
    R(13, 5, 1, 1, "#b991ff");
    R(3, 10, 1, 1, "#4deeea");
    R(12, 10, 1, 1, "#bfffff");
    ctx.restore();
  },

  _drawPitfall(ctx, x, y, cellPx) {
    const u = cellPx / 16;
    const px = (n) => Math.round(n * u);
    const R = (gx, gy, gw, gh, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(x + px(gx), y + px(gy), px(gw), px(gh));
    };

    ctx.save();
    ctx.imageSmoothingEnabled = false;

    // マップ上で実際に使われる落とし穴スプライト。
    // 普通の黒い穴ではなく、AIシミュレーション空間が欠損した
    // 「電子空間へ吸い込まれるデータホール」として描く。
    // ※判定・座標・サイズ・アニメーションは変更しない。
    ctx.shadowColor = "rgba(77,238,234,0.72)";
    ctx.shadowBlur = Math.max(5, cellPx * 0.18);
    R(3, 4, 10, 8, "rgba(77,238,234,0.12)");
    R(4, 3, 8, 10, "rgba(143,95,255,0.14)");
    ctx.shadowBlur = 0;

    // 壊れた仮想床の外周。床に馴染みつつ、周囲だけネオンで危険感を出す。
    R(4, 3, 8, 1, "#1f3767");
    R(3, 4, 10, 1, "#14264d");
    R(2, 5, 12, 2, "#0d1a38");
    R(2, 7, 12, 3, "#09142e");
    R(3, 10, 10, 2, "#0d1a38");
    R(4, 12, 8, 1, "#14264d");

    // 中央の吸い込み口。黒ベタにせず、紫〜紺の渦として読ませる。
    R(6, 5, 4, 1, "#6a3cff");
    R(5, 6, 6, 1, "#322a78");
    R(4, 7, 8, 1, "#151846");
    R(5, 8, 6, 2, "#050814");
    R(6, 10, 4, 1, "#0b1030");
    R(7, 11, 2, 1, "#02040b");

    // ポップな8bitネオンリング。遠目でも「普通の床ではない」と分かる輪郭。
    R(6, 3, 4, 1, "#bfffff");
    R(4, 4, 2, 1, "#4deeea");
    R(10, 4, 2, 1, "#b991ff");
    R(3, 5, 1, 3, "#4deeea");
    R(12, 5, 1, 3, "#8a56ff");
    R(3, 9, 1, 2, "#8a56ff");
    R(12, 9, 1, 2, "#4deeea");
    R(4, 12, 3, 1, "#b991ff");
    R(9, 12, 3, 1, "#4deeea");

    // 吸い込み渦。少ないドットでサイバーな回転感を出す。
    R(7, 6, 3, 1, "#e4d4ff");
    R(9, 7, 2, 1, "#4deeea");
    R(6, 8, 4, 1, "#8a56ff");
    R(5, 9, 2, 1, "#4deeea");
    R(7, 10, 3, 1, "#b991ff");

    // データ欠損・グリッチ破片。右上の参考デザインのような電子崩壊感を追加。
    R(1, 4, 2, 1, "#4deeea");
    R(13, 3, 1, 1, "#ff2e6d");
    R(14, 6, 1, 1, "#b991ff");
    R(1, 10, 2, 1, "#8a56ff");
    R(13, 11, 2, 1, "#4deeea");
    R(5, 14, 1, 1, "#ff2e6d");
    R(10, 1, 1, 1, "#4deeea");
    R(12, 13, 1, 1, "#bfffff");

    // 仮想床のひび割れ。落とし穴というより「床データの破損」に見せる。
    R(4, 6, 1, 1, "#26346d");
    R(5, 7, 1, 1, "#26346d");
    R(10, 6, 1, 1, "#26346d");
    R(11, 5, 1, 1, "#26346d");
    R(4, 11, 1, 1, "#26346d");
    R(11, 10, 1, 1, "#26346d");

    // 小さなハイライト。可愛くポップな8bit感を残す。
    R(4, 4, 1, 1, "#ffffff");
    R(11, 11, 1, 1, "#bfffff");
    ctx.restore();
  },

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
   画面切り替え・HUD更新・ポップアップ・REC表示・SYSTEM BOOT演出・
   エンディング演出など、DOM操作を一手に引き受けるクラス。
================================================================ */
class UIManager {
  showScreen(screenId) {
    document.querySelectorAll(".screen").forEach((el) => {
      if (el.id === screenId) el.classList.add("active");
      else el.classList.remove("active");
    });
    this.resetScrollPositions();
  }

  resetScrollPositions() {
    window.scrollTo(0, 0);
    document.documentElement.scrollTop = 0;
    document.body.scrollTop = 0;
    document.querySelectorAll(".screen, .crt-frame, .result-scroll, .ending-console").forEach((el) => {
      el.scrollTop = 0;
      el.scrollLeft = 0;
    });
  }

  clearTransientMessages() {
    const floating = document.getElementById("floating-message");
    if (floating) {
      floating.textContent = "";
      floating.classList.add("hidden");
      floating.style.animation = "none";
      void floating.offsetWidth;
      floating.style.animation = "";
    }
    const treasurePopup = document.getElementById("treasure-popup");
    if (treasurePopup) {
      treasurePopup.classList.add("hidden");
      treasurePopup.classList.remove("show");
    }
    const labPopup = document.getElementById("lab-popup");
    if (labPopup) {
      labPopup.classList.add("hidden");
      labPopup.classList.remove("show");
    }
    const settingsFeedback = document.getElementById("settings-feedback");
    if (settingsFeedback) settingsFeedback.classList.add("hidden");
    const endingLog = document.getElementById("ending-log");
    if (endingLog) endingLog.textContent = "";
    const endingPrompt = document.getElementById("ending-prompt");
    if (endingPrompt) endingPrompt.classList.add("hidden");
  }

  updateSteps(steps) { document.getElementById("hud-steps").textContent = steps; }
  updateTimer(seconds) { document.getElementById("hud-timer").textContent = formatTime(seconds); }
  updateMission(text) { document.getElementById("hud-mission").textContent = text; }

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
    popup.classList.remove("show");
    void popup.offsetWidth;
    popup.classList.add("show");
    setTimeout(() => { popup.classList.add("hidden"); popup.classList.remove("show"); }, 1800);
  }

  showFloatingMessage(text) {
    const el = document.getElementById("floating-message");
    el.textContent = text;
    el.classList.remove("hidden");
    el.style.animation = "none";
    void el.offsetWidth;
    el.style.animation = "";
  }

  setRecRecording() {
    const el = document.getElementById("rec-indicator");
    el.classList.remove("hidden", "stopped");
    document.getElementById("rec-text").textContent = "REC ● OBSERVING";
  }
  setRecStopped() {
    const el = document.getElementById("rec-indicator");
    el.classList.remove("hidden");
    el.classList.add("stopped");
    document.getElementById("rec-text").textContent = "REC ■ ANALYSIS DONE";
  }
  hideRec() { document.getElementById("rec-indicator").classList.add("hidden"); }

  showLabBadge(subjectId) {
    document.getElementById("lab-id-number").textContent = subjectId;
    document.getElementById("lab-id-badge").classList.remove("hidden");
  }
  hideLabBadge() { document.getElementById("lab-id-badge").classList.add("hidden"); }

  /** ②SYSTEM BOOT演出（初回起動時のみ、約3秒） */
  playBootSequence() {
    return new Promise((resolve) => {
      const lines = ["boot-line-1", "boot-line-2", "boot-line-3", "boot-line-3b"];
      lines.forEach((id, i) => {
        setTimeout(() => document.getElementById(id).classList.add("show"), 200 + i * 350);
      });
      setTimeout(() => {
        document.getElementById("boot-bar-inner").style.width = "100%";
      }, 500);
      setTimeout(() => document.getElementById("boot-line-4").classList.add("show"), 2500);
      setTimeout(() => document.getElementById("boot-line-5").classList.add("show"), 2850);
      setTimeout(resolve, 3200);
    });
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

  /** ⑧エンディング演出：「実はこういうゲームでした」の種明かし */
  playRevealSequence() {
    return new Promise((resolve) => {
      this.showScreen("screen-reveal");
      const el = document.getElementById("reveal-line");
      const lines = [
        { text: "……解析が完了しました。", emphasis: false },
        { text: "実はこのゲームは、", emphasis: false },
        { text: "「ダンジョンで宝を探すゲーム」ではありませんでした。", emphasis: false },
        { text: "あなたは、AI研究所の被験者でした。", emphasis: true },
        { text: "MISSION COMPLETE", emphasis: true },
        { text: "Behavior Analysis Finished", emphasis: true },
      ];
      let i = 0;
      const showNext = () => {
        if (i >= lines.length) { setTimeout(resolve, 400); return; }
        const { text, emphasis } = lines[i];
        el.textContent = text;
        el.classList.toggle("emphasis", emphasis);
        el.classList.remove("show");
        void el.offsetWidth;
        el.classList.add("show");
        i++;
        setTimeout(showNext, 1800);
      };
      showNext();
    });
  }
}


/* ================================================================
   EndingManager
   ----------------------------------------------------------------
   ⑪診断結果画面を「終える」ときにだけ流れる、研究所コンソール風の
   エンディング演出を専門に担当するクラス。タイプライター表示・
   点滅カーソル・ENTER/SPACE/タップでのスキップ・展示モードでの
   自動タイムアウトをすべてここに閉じ込めている。
================================================================ */
class EndingManager {
  constructor() {
    this.IDLE_TIMEOUT_MS = 180000; // 展示モード：3分操作が無ければ自動でタイトルへ
    this.CHAR_DELAY_MS = 28;
    this.LINE_PAUSE_MS = 380;
  }

  /**
   * エンディングを再生する。ENTER/SPACE/タップ、または3分の無操作で
   * 解決(resolve)される Promise を返す。
   * @param {string} subjectId 今回の被験者No.
   */
  play(subjectId, options = {}) {
    return new Promise((resolve) => {
      const fast = !!options.fast;
      const logEl = document.getElementById("ending-log");
      const promptEl = document.getElementById("ending-prompt");
      logEl.textContent = "";
      promptEl.classList.add("hidden");

      const normalLines = [
        "━━━━━━━━━━━━━━",
        "Experiment Finished",
        "━━━━━━━━━━━━━━",
        "被験者No.",
        String(subjectId),
        "━━━━━━━━━━━━━━",
        "行動データ",
        "保存しました。",
        "━━━━━━━━━━━━━━",
        "AI学習モデルへ",
        "探索データを送信しました。",
        "━━━━━━━━━━━━━━",
        "ご協力ありがとうございました。",
        "━━━━━━━━━━━━━━",
        "STATUS",
        "COMPLETE",
        "━━━━━━━━━━━━━━",
      ];
      const fastLines = [
        "━━━━━━━━━━━━━━",
        "Experiment Finished",
        "━━━━━━━━━━━━━━",
        "被験者No.",
        String(subjectId),
        "━━━━━━━━━━━━━━",
        "行動データ",
        "保存しました。",
        "━━━━━━━━━━━━━━",
        "ご協力ありがとうございました。",
        "━━━━━━━━━━━━━━",
        "STATUS",
        "COMPLETE",
        "━━━━━━━━━━━━━━",
      ];
      const lines = fast ? fastLines : normalLines;
      const charDelay = fast ? Math.max(8, Math.round(this.CHAR_DELAY_MS * 0.45)) : this.CHAR_DELAY_MS;
      const linePause = fast ? Math.max(90, Math.round(this.LINE_PAUSE_MS * 0.45)) : this.LINE_PAUSE_MS;
      const promptDelay = fast ? 700 : 3000;

      let finished = false;
      let charTimerHandle = null;
      let idleTimeoutHandle = null;

      const cleanup = () => {
        if (finished) return;
        finished = true;
        if (charTimerHandle) clearTimeout(charTimerHandle);
        if (idleTimeoutHandle) clearTimeout(idleTimeoutHandle);
        window.removeEventListener("keydown", onKey);
        window.removeEventListener("pointerdown", onPointer);
      };
      const finishNow = () => { cleanup(); resolve(); };
      const onKey = (e) => {
        if (!promptEl.classList.contains("hidden") && (e.key === "Enter" || e.key === " ")) finishNow();
      };
      const onPointer = () => {
        if (!promptEl.classList.contains("hidden")) finishNow();
      };
      window.addEventListener("keydown", onKey);
      window.addEventListener("pointerdown", onPointer);

      // ⑨展示モード：万一プロンプトが出た後も操作が無ければ、3分で強制的に終える
      idleTimeoutHandle = setTimeout(finishNow, this.IDLE_TIMEOUT_MS);

      // ---- タイプライター表示 ----
      let lineIndex = 0;
      let charIndex = 0;
      const typeStep = () => {
        if (finished) return;
        if (lineIndex >= lines.length) {
          setTimeout(() => {
            if (finished) return;
            promptEl.classList.remove("hidden");
          }, promptDelay);
          return;
        }
        const line = lines[lineIndex];
        if (charIndex === 0 && logEl.textContent.length > 0) logEl.textContent += "\n";
        logEl.textContent += line[charIndex];
        charIndex++;
        if (charIndex >= line.length) {
          lineIndex++;
          charIndex = 0;
          charTimerHandle = setTimeout(typeStep, linePause);
        } else {
          charTimerHandle = setTimeout(typeStep, charDelay);
        }
      };
      typeStep();
    });
  }
}


/* ================================================================
   ResultRenderer
   ----------------------------------------------------------------
   診断結果画面・統計ページ・診断カード・アルゴリズム解説画面への
   データ描画をまとめて担当する「見た目専門」のクラス。
================================================================ */
class ResultRenderer {
  /** 診断結果画面を描画する（⑤みんなの平均との比較つき） */
  renderResult(record, maze, player, averages) {
    document.getElementById("result-title").textContent = record.title;
    document.getElementById("result-ai-comment").textContent = record.comment;
    document.getElementById("result-subject-id").textContent = record.pid;

    this._animateBar("bar-dfs", "pct-dfs", record.dfsScore);
    this._animateBar("bar-bfs", "pct-bfs", record.bfsScore);
    this._animateBar("bar-linear", "pct-linear", record.linearScore);

    this._renderCompareLine("compare-dfs", record.dfsScore, averages ? averages.avgDfs : null);
    this._renderCompareLine("compare-bfs", record.bfsScore, averages ? averages.avgBfs : null);
    this._renderCompareLine("compare-linear", record.linearScore, averages ? averages.avgLinear : null);

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

  _renderCompareLine(elementId, myScore, avgScore) {
    const el = document.getElementById(elementId);
    if (avgScore === null || avgScore === undefined) {
      el.textContent = "まだ比較できるデータがありません（あなたが最初の被験者です）";
      el.className = "compare-line";
      return;
    }
    const diff = Math.round(myScore - avgScore);
    const avgRounded = Math.round(avgScore);
    if (diff > 2) {
      el.textContent = `みんな ${avgRounded}% ／ 平均より ${diff}% 高いです`;
      el.className = "compare-line higher";
    } else if (diff < -2) {
      el.textContent = `みんな ${avgRounded}% ／ 平均より ${Math.abs(diff)}% 低いです`;
      el.className = "compare-line lower";
    } else {
      el.textContent = `みんな ${avgRounded}% ／ 平均とほぼ同じです`;
      el.className = "compare-line";
    }
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

  /** ⑥アルゴリズム解説画面の「今回あなたがなぜこの診断だったか」欄 */
  renderExplainPersonal(record) {
    document.getElementById("explain-your-title").textContent = record.title;
    const list = document.getElementById("explain-reasons");
    list.innerHTML = (record.reasoning || [])
      .map((reason) => `<li>${reason}</li>`)
      .join("");
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

    return { title, comment };
  }

  /**
   * ⑨SNS投稿を意識した「画像として保存」用のカードをcanvasに描画する。
   * html2canvas等の外部ライブラリは使わず、Canvas 2D APIで直接描画する。
   */
  renderShareCardImage(canvas, cardData, titleText, commentText) {
    const W = 720, H = 900;
    canvas.width = W;
    canvas.height = H;
    const ctx = canvas.getContext("2d");

    // 背景（研究所レポート風のグラデーション＋グリッド）
    const grad = ctx.createLinearGradient(0, 0, W, H);
    grad.addColorStop(0, "#0d1424");
    grad.addColorStop(1, "#05070d");
    ctx.fillStyle = grad;
    ctx.fillRect(0, 0, W, H);

    ctx.strokeStyle = "rgba(77,238,234,0.08)";
    ctx.lineWidth = 1;
    for (let x = 0; x < W; x += 24) { ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, H); ctx.stroke(); }
    for (let y = 0; y < H; y += 24) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke(); }

    // 四隅の装飾枠
    ctx.strokeStyle = "#ffce54";
    ctx.lineWidth = 4;
    const cornerLen = 30, pad = 24;
    [[pad, pad, 1, 1], [W - pad, pad, -1, 1], [pad, H - pad, 1, -1], [W - pad, H - pad, -1, -1]].forEach(([cx, cy, sx, sy]) => {
      ctx.beginPath();
      ctx.moveTo(cx, cy + cornerLen * sy);
      ctx.lineTo(cx, cy);
      ctx.lineTo(cx + cornerLen * sx, cy);
      ctx.stroke();
    });

    ctx.textAlign = "left";
    ctx.fillStyle = "#4deeea";
    ctx.font = "bold 20px monospace";
    ctx.fillText("ALGORITHM RESEARCH LAB", 50, 80);
    ctx.fillStyle = "#7c8bb0";
    ctx.font = "14px monospace";
    ctx.fillText("診断カード / DIAGNOSTIC REPORT", 50, 106);

    ctx.fillStyle = "#ffce54";
    ctx.font = "bold 40px monospace";
    ctx.fillText(titleText, 50, 170);

    // コメントの折り返し表示（日本語は文字数ベースで簡易ラップ）
    ctx.fillStyle = "#e7f1ff";
    ctx.font = "18px monospace";
    const wrapped = this._wrapJapanese(commentText, 20);
    wrapped.forEach((line, i) => ctx.fillText(line, 50, 210 + i * 26));

    // スコアバー
    const barsTop = 210 + wrapped.length * 26 + 40;
    const bars = [
      { label: "DFS", value: Number(cardData.dfsScore) || 0, color: "#ff2e6d" },
      { label: "BFS", value: Number(cardData.bfsScore) || 0, color: "#4deeea" },
      { label: "線形探索", value: Number(cardData.linearScore) || 0, color: "#ffce54" },
    ];
    bars.forEach((bar, i) => {
      const y = barsTop + i * 56;
      ctx.fillStyle = "#7c8bb0";
      ctx.font = "14px monospace";
      ctx.fillText(bar.label, 50, y - 8);
      ctx.fillStyle = "#121b30";
      ctx.fillRect(50, y, W - 180, 20);
      ctx.fillStyle = bar.color;
      ctx.fillRect(50, y, (W - 180) * clamp(bar.value, 0, 100) / 100, 20);
      ctx.fillStyle = "#e7f1ff";
      ctx.font = "bold 14px monospace";
      ctx.fillText(bar.value + "%", W - 110, y + 16);
    });

    const statsY = barsTop + bars.length * 56 + 30;
    ctx.fillStyle = "#7c8bb0";
    ctx.font = "14px monospace";
    ctx.fillText(`クリアタイム: ${formatTime(cardData.elapsedSeconds)}　歩数: ${cardData.steps}`, 50, statsY);

    ctx.fillStyle = "#4deeea";
    ctx.font = "16px monospace";
    ctx.fillText(`SUBJECT NO. ${cardData.pid}`, 50, H - 50);
  }

  _wrapJapanese(text, maxChars) {
    const lines = [];
    let cur = "";
    for (const ch of text || "") {
      cur += ch;
      if (cur.length >= maxChars) { lines.push(cur); cur = ""; }
    }
    if (cur) lines.push(cur);
    return lines.slice(0, 4);
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

    this._renderRankingList("stats-title-ranking", stats.titleRanking,
      (item) => `<span class="rank-name">${item.title}</span><span class="rank-value">${item.count}人</span>`);
    this._renderRankingList("stats-fastest-ranking", stats.fastestRanking,
      (item) => `<span class="rank-name">被験者${item.pid}（${item.title}）</span><span class="rank-value">${formatTime(item.elapsedSeconds)}</span>`);
    this._renderRankingList("stats-exploration-ranking", stats.explorationRanking,
      (item) => `<span class="rank-name">被験者${item.pid}（${item.title}）</span><span class="rank-value">${item.explorationRate}%</span>`);

    this._renderRecentTable(stats.recent);
  }

  _renderRankingList(elementId, items, lineBuilder) {
    const el = document.getElementById(elementId);
    if (!items || items.length === 0) {
      el.innerHTML = `<li class="ranking-empty">まだ記録がありません。最初のデータ提供者になろう！</li>`;
      return;
    }
    el.innerHTML = items.map((item) => `<li>${lineBuilder(item)}</li>`).join("");
  }

  _renderRecentTable(recent) {
    const tbody = document.getElementById("stats-recent-table-body");
    if (!recent || recent.length === 0) {
      tbody.innerHTML = `<tr><td colspan="5" class="ranking-empty">まだ記録がありません。</td></tr>`;
      return;
    }
    tbody.innerHTML = recent.map((r) => `
      <tr>
        <td>${r.pid}</td>
        <td>${r.title}</td>
        <td>${r.typeCode}</td>
        <td>${formatTime(r.elapsedSeconds)}</td>
        <td>${r.steps}</td>
      </tr>
    `).join("");
  }
}


/* ================================================================
   GameManager
   ----------------------------------------------------------------
   すべてのクラスをつなぎ合わせ、SYSTEM BOOT→タイトル→ゲーム→
   解析演出→エンディング演出→結果→統計、という一連の流れを制御する
   司令塔。⑪展示モード（3分無操作でタイトルへ自動復帰）もここで管理する。
================================================================ */
class GameManager {
  constructor() {
    this.COLS = 11;
    this.ROWS = 9;
    this.IDLE_TIMEOUT_MS = 180000;

    this.ui = new UIManager();
    this.storage = new StorageManager();
    this.statistics = new StatisticsManager(this.storage);
    this.resultRenderer = new ResultRenderer();
    this.logManager = new LogManager();
    this.settings = new SettingsManager();
    this.endingManager = new EndingManager();

    this.maze = null;
    this.player = null;
    this.revealed = new Set();
    this.cellPx = 40;

    this.timerHandle = null;
    this.animHandle = null;
    this.idleCheckHandle = null;
    this.idleReturning = false;
    this.inputLocked = false;

    this.subjectId = generateSubjectId(); // ③START/リスタート時に必ず更新される
    this.lastRecord = null;
    this.lastCardData = null; // 診断カード画面に表示中のデータ（画像保存ボタン用）
  }

  init() {
    document.getElementById("btn-start").addEventListener("click", () => this.startNewGame());
    document.getElementById("btn-howto").addEventListener("click", () => this.ui.showScreen("screen-howto"));
    document.getElementById("btn-howto-back").addEventListener("click", () => this.ui.showScreen("screen-title"));
    document.getElementById("btn-history").addEventListener("click", () => this.showStats());
    document.getElementById("btn-retry").addEventListener("click", () => this.startNewGame());
    // ⑪診断結果画面から「タイトルへ」を押した時だけ、エンディング演出を挟む
    document.getElementById("btn-title").addEventListener("click", () => this._finishAndGoToTitle());
    document.getElementById("btn-stats").addEventListener("click", () => this.showStats());
    document.getElementById("btn-stats-back").addEventListener("click", () => this.ui.showScreen("screen-result"));
    document.getElementById("btn-stats-title").addEventListener("click", () => this.goToTitle());
    document.getElementById("btn-explain").addEventListener("click", () => this.showExplain());
    document.getElementById("btn-explain-back").addEventListener("click", () => this.ui.showScreen("screen-result"));
    document.getElementById("btn-card-download").addEventListener("click", () => this.downloadCardImage());

    // ④設定画面
    document.getElementById("btn-settings").addEventListener("click", () => this.showSettings());
    document.getElementById("btn-settings-back").addEventListener("click", () => this.ui.showScreen("screen-title"));
    document.getElementById("btn-toggle-reduce-motion").addEventListener("click", () => this._toggleReduceMotion());
    document.getElementById("btn-clear-history").addEventListener("click", () => this._confirmClearHistory());
    this._applyReduceMotionSetting();

    window.addEventListener("keydown", (e) => this._handleKey(e));
    document.querySelectorAll(".dpad-btn").forEach((btn) => {
      const fire = (ev) => { ev.preventDefault(); this.tryMove(btn.dataset.dir); };
      btn.addEventListener("click", fire);
      btn.addEventListener("touchstart", fire, { passive: false });
    });

    window.addEventListener("resize", () => this._resizeCanvases());

    // ⑨展示モード：どんな操作でも「最後に操作した時刻」を更新する
    this.lastInteraction = Date.now();
    const resetIdle = () => { this.lastInteraction = Date.now(); };
    window.addEventListener("keydown", resetIdle, true);
    window.addEventListener("pointerdown", resetIdle, true);
    window.addEventListener("touchstart", resetIdle, true);
    this.idleCheckHandle = setInterval(() => this._checkIdle(), 1000);
  }

  /** 設定画面を開く（現在の設定値を反映してから表示する） */
  showSettings() {
    this._refreshSettingsScreen();
    this.ui.showScreen("screen-settings");
  }
  _refreshSettingsScreen() {
    const on = this.settings.get("reduceMotion");
    const btn = document.getElementById("btn-toggle-reduce-motion");
    btn.textContent = on ? "アニメーション軽減：ON" : "アニメーション軽減：OFF";
  }
  _toggleReduceMotion() {
    this.settings.toggle("reduceMotion");
    this._applyReduceMotionSetting();
    this._refreshSettingsScreen();
  }
  _applyReduceMotionSetting() {
    document.body.classList.toggle("reduce-motion-pref", !!this.settings.get("reduceMotion"));
  }
  _confirmClearHistory() {
    const label = document.getElementById("btn-clear-history");
    if (label.dataset.confirming === "1") {
      this.storage.clearAllResults();
      label.dataset.confirming = "0";
      label.textContent = "履歴をリセットする";
      const feedback = document.getElementById("settings-feedback");
      feedback.textContent = "履歴をリセットしました。";
      feedback.classList.remove("hidden");
    } else {
      label.dataset.confirming = "1";
      label.textContent = "本当に消去する？（もう一度押す）";
    }
  }

  goToTitle() {
    this._stopTimer();
    this.logManager.stop();
    this.ui.clearTransientMessages();
    this.ui.hideLabBadge();
    this.ui.hideRec();
    this.inputLocked = false;
    this.ui.showScreen("screen-title");
  }

  /** ⑪結果画面から離れるときだけ、研究所コンソール風のエンディングを挟んでからタイトルへ戻る */
  async _finishAndGoToTitle() {
    this._stopTimer();
    this.logManager.stop();
    this.ui.hideLabBadge();
    this.ui.hideRec();
    this.ui.clearTransientMessages();
    this.ui.showScreen("screen-ending");
    await this.endingManager.play(this.subjectId);
    this.goToTitle();
  }

  async _checkIdle() {
    const activeScreen = document.querySelector(".screen.active");
    if (!activeScreen || this.idleReturning) return;
    const exempt = ["screen-title", "screen-boot", "screen-briefing", "screen-ending"];
    if (exempt.includes(activeScreen.id)) return;
    if (Date.now() - this.lastInteraction > this.IDLE_TIMEOUT_MS) {
      this.idleReturning = true;
      this._stopTimer();
      this.logManager.stop();
      this.ui.clearTransientMessages();
      this.ui.hideLabBadge();
      this.ui.hideRec();
      this.inputLocked = true;
      this.ui.showScreen("screen-ending");
      await this.endingManager.play(this.subjectId || "------", { fast: true });
      this.goToTitle();
      this.lastInteraction = Date.now();
      this.idleReturning = false;
    }
  }

  startNewGame() {
    this._stopTimer();
    this.logManager.stop();
    this.ui.clearTransientMessages();
    this.ui.resetScrollPositions();
    this.lastInteraction = Date.now();
    // ③STARTのたびに新しい被験者No.を発行する（過去の履歴は書き換えない）
    this.subjectId = generateSubjectId();
    this.ui.showLabBadge(this.subjectId);
    this.ui.setRecRecording();
    this.logManager.startTicker("lab-log-ticker");
    this.logManager.startPopups("lab-popup");

    this.maze = new MazeGenerator(this.COLS, this.ROWS);
    this.player = new PlayerController(this.maze);
    this.revealed = new Set();
    this._revealCellAndNeighbors(0, 0);
    this.inputLocked = false;
    this.player.moving = false;

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
    if (!result.moved) {
      if (result.message) this.ui.showFloatingMessage(result.message);
      return;
    }

    this.ui.updateSteps(this.player.totalSteps);

    if (result.treasureJustCollected) {
      this.ui.setTreasureAcquired(true);
      this.ui.showTreasurePopup();
      this.ui.updateMission("ゴールを目指そう");
    } else if (result.message) {
      this.ui.showFloatingMessage(result.message);
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

  /** クリア後：データ収集→解析→結果画面、という一連の流れ */
  async _onGameClear() {
    this.inputLocked = true;
    this.player.stopClock();
    this._stopTimer();
    this.logManager.stop();

    await this.ui.playAnalyzingSequence();
    this.ui.setRecStopped();
    await this._buildAndShowResult();
  }

  async _buildAndShowResult() {
    const analysis = Analyzer.analyze(this.player);

    const record = {
      id: generateRecordId(),
      pid: this.subjectId,
      typeCode: analysis.typeCode,
      titleIndex: analysis.titleIndex,
      commentIndex: analysis.commentIndex,
      title: analysis.title,
      comment: analysis.comment,
      reasoning: analysis.reasoning,
      dfsScore: analysis.dfsScore,
      bfsScore: analysis.bfsScore,
      linearScore: analysis.linearScore,
      steps: analysis.stats.totalSteps,
      stepDiff: analysis.stats.stepDiff,
      explorationRate: analysis.stats.explorationRate,
      elapsedSeconds: analysis.stats.elapsedSeconds,
      gimmicks: analysis.gimmicks,
      timestamp: Date.now(),
    };
    this.lastRecord = record;

    // ⑤平均比較のために、保存する「前」の平均を取得しておく
    // （自分の結果を混ぜる前の、これまでの被験者たちの平均と比較するため）
    const averages = await this.statistics.getAverageScores();

    await this.storage.saveResult(record);

    this.resultRenderer.renderResult(record, this.maze, this.player, averages);

    const cardUrl = QRManager.buildCardUrl(record);
    QRManager.renderInto(
      document.getElementById("qr-canvas-wrap"),
      document.getElementById("qr-fallback-url"),
      cardUrl
    );

    this.ui.showScreen("screen-result");
  }

  async showStats() {
    const stats = await this.statistics.getAggregateStats();
    this.resultRenderer.renderStats(stats);
    this.ui.showScreen("screen-stats");
  }

  /** ⑥アルゴリズム解説画面（直近の診断結果があれば、根拠つきで表示） */
  showExplain() {
    if (this.lastRecord) this.resultRenderer.renderExplainPersonal(this.lastRecord);
    this.ui.showScreen("screen-explain");
  }

  /** ⑨診断カードを画像として保存する */
  downloadCardImage() {
    if (!this.lastCardData) return;
    const canvas = document.getElementById("card-share-canvas");
    this.resultRenderer.renderShareCardImage(
      canvas, this.lastCardData, this.lastCardData._title, this.lastCardData._comment
    );
    const link = document.createElement("a");
    link.download = `algolab_card_${this.lastCardData.pid}.png`;
    link.href = canvas.toDataURL("image/png");
    link.click();
  }

  /** URLのクエリに診断カード情報が含まれていれば、カード画面を直接表示する */
  async tryShowCardFromUrl() {
    const cardData = QRManager.parseCardParams(location.search);
    if (!cardData) return false;

    if (cardData.idOnly) {
      const found = await this.storage.getResultById(cardData.id);
      if (found) {
        const full = {
          typeCode: found.typeCode, titleIndex: found.titleIndex, commentIndex: found.commentIndex,
          dfsScore: found.dfsScore, bfsScore: found.bfsScore, linearScore: found.linearScore,
          elapsedSeconds: found.elapsedSeconds, steps: found.steps, pid: found.pid,
        };
        const { title, comment } = this.resultRenderer.renderCard(full);
        this.lastCardData = { ...full, _title: title, _comment: comment };
        this.ui.showScreen("screen-card");
        return true;
      }
      document.getElementById("card-title").textContent = "記録が見つかりませんでした";
      document.getElementById("card-comment").textContent =
        "この端末には診断データが保存されていません。QRコードを発行した端末でお試しください。";
      this.ui.showScreen("screen-card");
      return true;
    }

    const { title, comment } = this.resultRenderer.renderCard(cardData);
    this.lastCardData = { ...cardData, _title: title, _comment: comment };
    this.ui.showScreen("screen-card");
    return true;
  }
}




/* ================================================================
   Ver.1.7 UI/UXブラッシュアップ追加実装
   - START前の情報は「探索任務」に限定し、診断の真相はクリア後だけ表示
   - 研究資料メニュー、研究統計、称号資料、演出品質を強化
================================================================ */
(function applyVer17Patch() {
  const $ = (id) => document.getElementById(id);
  const safeText = (id, text) => { const el = $(id); if (el) el.textContent = text; };
  const safeHtml = (id, html) => { const el = $(id); if (el) el.innerHTML = html; };
  const esc = (v) => String(v ?? "").replace(/[&<>"]/g, (c) => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;"}[c]));

  function ensureCommentVolume() {
    const packs = {
      D: [
        "行き止まりを見つけるたび、研究員が『また奥まで行った！』とメモしていました。",
        "未知の通路を見ると足が勝手に進むタイプ。宝箱より好奇心の方が少し強めです。",
        "奥まで進んでから考える、ダンジョン向きの前のめり探索でした。",
        "あなたの探索ログは、まるで深さ優先探索の実演映像でした。",
        "『この先に何かある』を信じる力が強い。なお行き止まりもちゃんとあります。",
        "道の端まで確認する姿勢が光っています。研究所的にはサンプルが多くて助かります。",
        "分岐で迷うより、まず一本を攻める。潔い探索スタイルです。",
        "AIログ：被験者、通路の奥へ吸い込まれるように進行。好奇心レベル高。",
        "勇者ならたいまつを持って先頭を歩くタイプ。仲間は少し心配しています。",
        "行き止まりを回収する勢いがありました。スタンプラリーなら強いです。",
      ],
      B: [
        "無駄な移動を嫌う足取りでした。ダンジョンにも時短意識を持ち込むタイプです。",
        "近いところから整えていく、迷路界の片付け上手です。",
        "最短との差が小さく、研究員が『ナビ入ってる？』と疑いました。",
        "AIログ：到達効率が高い。無駄足に対する許容値が低めです。",
        "ゴールまでの圧が強い。寄り道に厳しいタイプかもしれません。",
        "広く見てから動く、落ち着いた探索判断が出ていました。",
        "RPGなら地図係。パーティ全員を迷わせない人です。",
        "宝箱回収から脱出までの動きに、効率派の気配がありました。",
        "『回り道？それ必要ですか？』という声が聞こえるログでした。",
        "近道の匂いを嗅ぎ分ける探索でした。研究所の床より勘が鋭い。",
      ],
      L: [
        "確認してから進む。安全第一、でもちゃんと前に進む堅実スタイルです。",
        "一歩ずつ確かめる姿勢が強め。ダンジョンでも指差し確認しそうです。",
        "探索順に一定のクセがありました。AIにはかなり観測しやすい被験者です。",
        "同じ場所の再確認も含めて、慎重なログが取れました。",
        "『念のため』が多めの探索。文化祭展示ではかなり信頼できるタイプです。",
        "RPGなら宝箱を開ける前に周囲を三回見るタイプ。罠チェック大事。",
        "焦らず順番に進む姿勢が、線形探索の考え方とよく似ています。",
        "AIログ：手順の再現性あり。被験者はかなり律儀です。",
        "抜け道より手順。冒険者というより優秀な点検係です。",
        "一つずつ見落としを潰す探索でした。研究員が安心して見ていられます。",
      ],
      X: [
        "深く、広く、丁寧に。探索アルゴリズムの全部盛り定食みたいなログでした。",
        "一つの型に収まらない動きです。AIが分類名で少し悩みました。",
        "効率も好奇心も確認力もあり、研究所側が一番おいしいデータを得ました。",
        "万能型です。迷路側が『どの罠で迷わせればいいの？』と困っています。",
        "RPGなら勇者・地図係・罠チェック係を一人で担当するタイプです。",
        "AIログ：複数の探索モデルに同時適合。ちょっと欲張りです。",
        "バランス感覚が高く、寄り道も脱出もほどよく成立していました。",
        "研究員コメント：これは展示向きのきれいな行動ログです。",
        "型がないのではなく、型を切り替えているような探索でした。",
        "アルゴリズム博士候補。次は研究員側に回ってほしいくらいです。",
      ],
      R: [
        "危ない床への警戒が見られました。研究所の安全講習を受けた人の動きです。",
        "慎重なのに止まらない。安全運転で宝箱まで行けるタイプです。",
        "危険回避センサーが働いていました。罠担当スタッフが少し悔しそうです。",
        "AIログ：危険床反応、良好。生存率が高そうな被験者です。",
        "RPGなら毒沼の前でちゃんと立ち止まれる人。えらい。",
        "無茶をせず、でも任務は完了する。現場向きの探索でした。",
        "落ち着いて周囲を見るクセがあり、危険回避タイプとして評価されました。",
        "研究員コメント：派手さより安定感。これはこれでかなり強いです。",
        "慎重派ですが臆病ではありません。進むべき時はちゃんと進んでいます。",
        "ダンジョンに保険をかけられるなら割引されそうな探索でした。",
      ],
      A: [
        "ワープも罠もイベントとして楽しむタイプ。研究所的には非常に見どころがあります。",
        "想定外の挙動が多めでした。AIがちょっと楽しそうにログを見ています。",
        "危険を踏んでも進む。RPGならイベント回収率が高い勇者です。",
        "AIログ：未知装置への反応あり。好奇心が安全確認を追い越しました。",
        "普通に歩けばいい場面で、なぜかドラマが生まれるタイプです。",
        "罠に落ちてもデータになる。展示作品としてはありがたい被験者です。",
        "転送装置への反応が記録されました。研究所のテンションが少し上がっています。",
        "型破りですが、退屈ではありません。迷路側も本気を出したくなる相手です。",
        "ショートカットか事故か、その境界を攻める探索でした。",
        "勇者というよりイベント発生装置。見ている側が飽きません。",
      ],
    };
    Object.entries(packs).forEach(([code, extra]) => {
      const key = code === "D" ? "COMMENT_POOL_D" : code === "B" ? "COMMENT_POOL_B" : code === "L" ? "COMMENT_POOL_L" : `COMMENT_POOL_${code}`;
      if (!Analyzer[key]) return;
      let n = 0;
      while (Analyzer[key].length < 45) {
        Analyzer[key].push(extra[n % extra.length]);
        n++;
      }
    });
  }
  ensureCommentVolume();

  function normalMissionPath(maze) {
    return maze.shortestPath(maze.start, maze.treasure).concat(maze.shortestPath(maze.treasure, maze.goal).slice(1));
  }
  function shortestPathWithWarp(maze, from, to) {
    const startKey = cellKey(from.c, from.r);
    const goalKey = cellKey(to.c, to.r);
    const q = [{ c: from.c, r: from.r }];
    const prev = new Map();
    const seen = new Set([startKey]);
    let head = 0;
    while (head < q.length) {
      const cur = q[head++];
      const curKey = cellKey(cur.c, cur.r);
      if (curKey === goalKey) break;
      const nexts = maze.neighborsOf(cur.c, cur.r).map((n) => ({ c: n.c, r: n.r }));
      const gimmick = maze.gimmickTypeAt(cur.c, cur.r);
      if (gimmick === "warpA" || gimmick === "warpB") {
        const dest = maze.warpDestination(gimmick);
        if (dest) nexts.push({ c: dest.c, r: dest.r, warp: true });
      }
      for (const n of nexts) {
        const nk = cellKey(n.c, n.r);
        if (seen.has(nk)) continue;
        seen.add(nk);
        prev.set(nk, { c: cur.c, r: cur.r });
        q.push({ c: n.c, r: n.r });
      }
    }
    if (!seen.has(goalKey)) return maze.shortestPath(from, to);
    const path = [];
    let cur = { c: to.c, r: to.r };
    path.push(cur);
    while (cellKey(cur.c, cur.r) !== startKey) {
      cur = prev.get(cellKey(cur.c, cur.r));
      if (!cur) break;
      path.push(cur);
    }
    return path.reverse();
  }
  function gimmickMissionPath(maze) {
    const a = shortestPathWithWarp(maze, maze.start, maze.treasure);
    const b = shortestPathWithWarp(maze, maze.treasure, maze.goal);
    return a.concat(b.slice(1));
  }
  function pathSteps(path) { return Math.max(0, (path || []).length - 1); }

  PlayerController.prototype.getTheoreticalShortestSteps = function() {
    const normal = normalMissionPath(this.maze);
    const gimmick = gimmickMissionPath(this.maze);
    return Math.min(pathSteps(normal), pathSteps(gimmick));
  };
  Object.defineProperty(PlayerController.prototype, "idealSteps", {
    configurable: true,
    get() { return this.getTheoreticalShortestSteps(); }
  });

  UIManager.prototype.playBootSequence = function() {
    return new Promise((resolve) => {
      this.showScreen("screen-boot");
      const lineMap = [
        ["boot-line-1", "SYSTEM BOOT..."],
        ["boot-line-2", "LAB SYSTEM ONLINE"],
        ["boot-line-3", "SUBJECT SESSION START"],
        ["boot-line-3b", ""],
        ["boot-line-4", "OK"],
        ["boot-line-5", "WELCOME SUBJECT"],
      ];
      lineMap.forEach(([id, text]) => {
        const el = $(id);
        if (el) { el.textContent = text; el.classList.remove("show"); }
      });
      const bar = $("boot-bar-inner");
      if (bar) bar.style.width = "0%";
      setTimeout(() => $("boot-line-1")?.classList.add("show"), 80);
      setTimeout(() => { if (bar) bar.style.width = "100%"; }, 180);
      setTimeout(() => $("boot-line-2")?.classList.add("show"), 320);
      setTimeout(() => $("boot-line-3")?.classList.add("show"), 560);
      setTimeout(() => $("boot-line-4")?.classList.add("show"), 820);
      setTimeout(() => $("boot-line-5")?.classList.add("show"), 980);
      setTimeout(resolve, 1250);
    });
  };

  UIManager.prototype.playBriefingSequence = function() {
    return new Promise((resolve) => {
      this.showScreen("screen-briefing");
      const logEl = $("briefing-log");
      const promptEl = $("briefing-prompt");
      if (!logEl || !promptEl) { resolve(); return; }
      logEl.textContent = "";
      promptEl.classList.add("hidden");
      const lines = [
        "━━━━━━━━━━━━━━",
        "MISSION BRIEFING",
        "研究施設 探索任務",
        "━━━━━━━━━━━━━━",
        "あなたの任務は",
        "ダンジョン内に眠る",
        "宝箱を回収し、",
        "脱出ポイントへ到達することです。",
        "━━━━━━━━━━━━━━",
        "注意事項",
        "・怪しい床には注意してください",
        "・転送装置が作動する場合があります",
        "・探索ルートは自由です",
        "━━━━━━━━━━━━━━",
        "準備完了",
      ];
      let lineIndex = 0, charIndex = 0, timer = null, ready = false, done = false;
      const cleanup = () => {
        if (done) return;
        done = true;
        if (timer) clearTimeout(timer);
        window.removeEventListener("keydown", onKey, true);
        window.removeEventListener("pointerdown", onPointer, true);
        window.removeEventListener("touchstart", onPointer, true);
      };
      const accept = (ev) => {
        if (!ready || done) return;
        if (ev) ev.preventDefault?.();
        cleanup();
        resolve();
      };
      const onKey = (e) => {
        if (e.key === "Enter" || e.key === " " || e.code === "Space") accept(e);
      };
      const onPointer = (e) => accept(e);
      window.addEventListener("keydown", onKey, true);
      window.addEventListener("pointerdown", onPointer, true);
      window.addEventListener("touchstart", onPointer, { capture: true, passive: false });
      const type = () => {
        if (done) return;
        if (lineIndex >= lines.length) {
          ready = true;
          promptEl.classList.remove("hidden");
          return;
        }
        const line = lines[lineIndex];
        if (charIndex === 0 && logEl.textContent.length > 0) logEl.textContent += "\n";
        if (charIndex < line.length) {
          logEl.textContent += line[charIndex++];
          timer = setTimeout(type, 12);
        } else {
          lineIndex++; charIndex = 0;
          timer = setTimeout(type, 90);
        }
      };
      type();
    });
  };

  EndingManager.prototype.play = function(subjectId, options = {}) {
    return new Promise((resolve) => {
      const fast = !!options.fast;
      const logEl = $("ending-log");
      const promptEl = $("ending-prompt");
      if (!logEl || !promptEl) { resolve(); return; }
      logEl.textContent = "";
      promptEl.classList.add("hidden");
      const lines = [
        "━━━━━━━━━━━━━━",
        "Experiment Finished",
        "━━━━━━━━━━━━━━",
        "被験者No.",
        String(subjectId || "------"),
        "━━━━━━━━━━━━━━",
        "行動データ",
        "保存しました。",
        "━━━━━━━━━━━━━━",
        ...(fast ? [] : ["研究端末から", "セッションを切断します。", "━━━━━━━━━━━━━━"]),
        "ご協力ありがとうございました。",
        "━━━━━━━━━━━━━━",
        "STATUS",
        "COMPLETE",
        "━━━━━━━━━━━━━━",
      ];
      let finished = false, timer = null, idle = null;
      const cleanup = () => {
        if (finished) return;
        finished = true;
        if (timer) clearTimeout(timer);
        if (idle) clearTimeout(idle);
        window.removeEventListener("keydown", onKey);
        window.removeEventListener("pointerdown", onPointer);
      };
      const finish = () => { cleanup(); resolve(); };
      const onKey = (e) => {
        if (!promptEl.classList.contains("hidden") && (e.key === "Enter" || e.key === " " || e.code === "Space")) finish();
      };
      const onPointer = () => { if (!promptEl.classList.contains("hidden")) finish(); };
      window.addEventListener("keydown", onKey);
      window.addEventListener("pointerdown", onPointer);
      idle = setTimeout(finish, this.IDLE_TIMEOUT_MS);
      let li = 0, ci = 0;
      const cd = fast ? 8 : 18, lp = fast ? 80 : 220;
      const type = () => {
        if (finished) return;
        if (li >= lines.length) {
          timer = setTimeout(() => promptEl.classList.remove("hidden"), fast ? 600 : 1200);
          return;
        }
        const line = lines[li];
        if (ci === 0 && logEl.textContent.length > 0) logEl.textContent += "\n";
        if (ci < line.length) {
          logEl.textContent += line[ci++];
          timer = setTimeout(type, cd);
        } else {
          li++; ci = 0; timer = setTimeout(type, lp);
        }
      };
      type();
    });
  };

  ResultRenderer.prototype._buildResearchEvaluation = function(record, player) {
    const diff = Math.max(0, record.stepDiff || 0);
    const rate = Number(record.explorationRate || 0);
    const revisit = player && player.totalSteps > 0 ? player.revisitCount / player.totalSteps : 0;
    let quality = 3;
    if (rate >= 70) quality++;
    if (rate >= 90 || (player && player.deadEndVisits >= 3)) quality++;
    if (record.steps < 8) quality--;
    quality = clamp(quality, 1, 5);
    let success = 92 + Math.min(7, Math.round(rate / 20)) - Math.min(8, Math.round(diff / 4));
    if (player?.warpUsed) success += 1;
    if (player?.pitfallHits) success += 1;
    success = clamp(success, 82, 99);
    const comments = [];
    if (rate >= 85) comments.push("豊富な探索データが得られました。研究員がニヤつく量です。");
    if (diff <= 2) comments.push("無駄の少ない経路で、効率性の高いサンプルです。");
    if (diff >= 12) comments.push("寄り道が多く、思考のクセが非常に観測しやすいログです。");
    if (player?.warpUsed > 0) comments.push("転送装置への反応も記録されました。未知装置への判断材料が増えています。");
    if (player?.pitfallHits > 0) comments.push("危険床への反応パターンを検出しました。罠担当が満足しています。");
    if (revisit > 0.25) comments.push("再訪が多く、確認行動の傾向が強く出ています。");
    if (player?.deadEndVisits >= 3) comments.push("行き止まり到達データが豊富です。深掘り傾向の分析に適しています。");
    if (player?.unexploredPriorityRatio > 0.65) comments.push("未探索マスを優先する傾向が強く、新規探索への反応が明確です。");
    if (comments.length === 0) comments.push("非常に興味深い被験者です。ほどよい探索ログが取得できました。");
    return { quality: "★★★★★".slice(0, quality) + "☆☆☆☆☆".slice(0, 5 - quality), success: `${Math.round(success)}%`, comment: pickRandom(comments) };
  };

  ResultRenderer.prototype._titleStats = function(record, aggregateStats) {
    const total = Math.max(1, aggregateStats?.totalPlayers || 1);
    const count = (aggregateStats?.titleRanking || []).find((x) => x.title === record.title)?.count || 1;
    const rate = (count / total) * 100;
    const sorted = [...(aggregateStats?.titleRanking || [])];
    let rank = sorted.findIndex((x) => x.title === record.title) + 1;
    if (rank <= 0) rank = sorted.length + 1;
    const rarity = rate <= 5 ? "★★★★★" : rate <= 12 ? "★★★★☆" : rate <= 25 ? "★★★☆☆" : rate <= 40 ? "★★☆☆☆" : "★☆☆☆☆";
    const comment = rate <= 8 ? "かなり珍しい探索タイプです。研究資料として価値が高いサンプルです。" : rate <= 20 ? "比較的珍しい探索タイプです。展示中に見かけたらちょっと当たりです。" : rate <= 35 ? "ほどよく観測される探索タイプです。研究所の基準データとして優秀です。" : "よく観測される探索タイプです。多くの人が近い判断をしています。";
    return { total, count, rate: Math.round(rate * 10) / 10, rank, rarity, comment };
  };

  ResultRenderer.prototype.renderResult = function(record, maze, player, averages, aggregateStats) {
    safeText("result-title", record.title);
    safeText("result-ai-comment", record.comment);
    safeText("result-subject-id", record.pid);
    safeText("result-subject-id-top", record.pid);
    this._animateBar("bar-dfs", "pct-dfs", record.dfsScore);
    this._animateBar("bar-bfs", "pct-bfs", record.bfsScore);
    this._animateBar("bar-linear", "pct-linear", record.linearScore);
    this._renderCompareLine("compare-dfs", record.dfsScore, averages ? averages.avgDfs : null);
    this._renderCompareLine("compare-bfs", record.bfsScore, averages ? averages.avgBfs : null);
    this._renderCompareLine("compare-linear", record.linearScore, averages ? averages.avgLinear : null);
    const reasons = record.reasoning || [];
    safeHtml("result-reasons", reasons.map((r) => `<li>${esc(r)}</li>`).join(""));
    safeText("stat-time", formatTime(record.elapsedSeconds));
    safeText("stat-steps", record.steps);
    safeText("stat-diff", (record.stepDiff >= 0 ? "+" : "") + record.stepDiff);
    safeText("stat-rate", record.explorationRate + "%");
    const normal = normalMissionPath(maze);
    const gimmick = gimmickMissionPath(maze);
    const normalSteps = pathSteps(normal);
    const gimmickSteps = pathSteps(gimmick);
    safeText("stat-normal-shortest", normalSteps);
    safeText("stat-gimmick-shortest", gimmickSteps);
    const notice = $("warp-shortest-notice");
    if (notice) {
      notice.className = "route-notice lab-alert";
      if ((record.gimmicks?.warpUsed || 0) > 0) {
        notice.textContent = "ワープ使用により、あなたの探索ルートに転送行動が記録されました。";
      } else if (gimmickSteps < normalSteps) {
        notice.textContent = "このマップでは、転送装置を使うと理論最短が短くなる可能性があります。";
      } else {
        notice.textContent = "このマップでは通常経路が理論最短として採用されました。";
      }
    }
    const evalData = this._buildResearchEvaluation(record, player);
    safeText("eval-quality", evalData.quality);
    safeText("eval-success", evalData.success);
    safeText("eval-comment", evalData.comment);
    const ts = this._titleStats(record, aggregateStats);
    safeText("research-current-title", record.title);
    safeText("research-title-count", `${ts.count}名 / ${ts.total}名中`);
    safeText("research-title-rate", `${ts.rate}%`);
    safeText("research-title-rarity", ts.rarity);
    safeText("research-title-comment", ts.comment);
    const playerCanvas = $("route-canvas-player");
    const normalCanvas = $("route-canvas-shortest");
    const gimmickCanvas = $("route-canvas-gimmick");
    if (playerCanvas) Renderer.drawRoute(playerCanvas, maze, player.path, "#4deeea");
    if (normalCanvas) Renderer.drawRoute(normalCanvas, maze, normal, "#ffce54");
    if (gimmickCanvas) Renderer.drawRoute(gimmickCanvas, maze, gimmick, "#72ff8a");
  };

  const TYPE_ARCHIVE = [
    ["D", "探究者", "DFSタイプ", "未知の道を最後まで進みやすいタイプ。", "行き止まりまで調べる／未探索ルートを優先する", "気になった道は最後まで見たい！"],
    ["B", "最短マスター", "BFSタイプ", "無駄な移動が少ない効率派。", "最短との差が少ない／後戻りが少ない", "回り道？それ、必要ですか？"],
    ["L", "慎重派", "線形探索タイプ", "一つずつ丁寧に確認するタイプ。", "順番に進む／再訪や確認が多い", "確認してから進む、それが安全。"],
    ["X", "アルゴリズム博士", "バランス型", "深さ・広さ・確認のバランスが取れた万能型。", "探索率も効率もほどよく高い", "全部わかる。たぶん研究員側。"],
    ["R", "危険回避タイプ", "安全重視型", "怪しい床や危険を避けつつ任務を進めるタイプ。", "落とし穴を避ける／慎重に周囲を見る", "石橋を叩いて、ちゃんと渡る。"],
    ["A", "型破りな挑戦者", "イベント回収型", "ワープや罠も含めてダンジョンを味わうタイプ。", "ワープ使用／落とし穴／想定外ルート", "安全確認より、イベント発生。"],
  ];

  ResultRenderer.prototype.renderTypeList = function(aggregateStats) {
    const total = Math.max(1, aggregateStats?.totalPlayers || 0);
    const typeCounts = {};
    (aggregateStats?.recent || []).forEach((r) => typeCounts[r.typeCode] = (typeCounts[r.typeCode] || 0) + 1);
    // recentだけでは足りないのでtypeRatioから概算復元
    Object.entries(aggregateStats?.typeRatio || {}).forEach(([k, pct]) => {
      typeCounts[k] = Math.max(typeCounts[k] || 0, Math.round((pct / 100) * total));
    });
    const ranked = Object.entries(typeCounts).sort((a,b)=>b[1]-a[1]).map(([k])=>k);
    const html = TYPE_ARCHIVE.map(([code, title, typeName, feature, behavior, quote]) => {
      const count = typeCounts[code] || 0;
      const rate = total > 0 ? Math.round((count / total) * 1000) / 10 : 0;
      const rank = ranked.indexOf(code) >= 0 ? ranked.indexOf(code) + 1 : "--";
      const rarity = rate <= 5 ? "★★★★★" : rate <= 12 ? "★★★★☆" : rate <= 25 ? "★★★☆☆" : rate <= 40 ? "★★☆☆☆" : "★☆☆☆☆";
      return `<article class="type-card">
        <div class="type-card-head"><span class="type-code">${code}</span><h3>${esc(title)}</h3></div>
        <p class="type-name">${esc(typeName)}</p>
        <div class="type-research-data">
          <span>獲得人数 <b>${count}名</b></span>
          <span>割合 <b>${rate}%</b></span>
          <span>人気順位 <b>${rank}位</b></span>
          <span>レア度 <b>${rarity}</b></span>
        </div>
        <p><strong>特徴</strong><br>${esc(feature)}</p>
        <p><strong>なりやすい行動</strong><br>${esc(behavior)}</p>
        <p class="type-quote">「${esc(quote)}」</p>
      </article>`;
    }).join("");
    safeHtml("type-list-grid", html);
  };

  GameManager.prototype.init = function() {
    const add = (id, event, fn) => { const el = $(id); if (el) el.addEventListener(event, fn); };
    add("btn-start", "click", () => this.startNewGame());
    add("btn-title", "click", () => this._finishAndGoToTitle());
    add("btn-stats", "click", () => this.showStats());
    add("btn-stats-back", "click", () => this.ui.showScreen("screen-result"));
    add("btn-stats-title", "click", () => this.goToTitle());
    add("btn-explain", "click", () => this.showExplain());
    add("btn-explain-menu", "click", () => this.showExplain());
    add("btn-explain-back", "click", () => this.ui.showScreen("screen-result"));
    add("btn-type-list", "click", () => this.showTypeList());
    add("btn-type-list-menu", "click", () => this.showTypeList());
    add("btn-type-list-back", "click", () => this.ui.showScreen("screen-result"));
    add("btn-card-download", "click", () => this.downloadCardImage());
    window.addEventListener("keydown", (e) => this._handleKey(e));
    document.querySelectorAll(".dpad-btn").forEach((btn) => {
      const fire = (ev) => { ev.preventDefault(); this.tryMove(btn.dataset.dir); };
      btn.addEventListener("click", fire);
      btn.addEventListener("touchstart", fire, { passive: false });
    });
    window.addEventListener("resize", () => this._resizeCanvases());
    this.lastInteraction = Date.now();
    const resetIdle = () => { this.lastInteraction = Date.now(); };
    window.addEventListener("keydown", resetIdle, true);
    window.addEventListener("pointerdown", resetIdle, true);
    window.addEventListener("touchstart", resetIdle, true);
    this.idleCheckHandle = setInterval(() => this._checkIdle(), 1000);
  };

  GameManager.prototype._prepareGameSession = function() {
    this._stopTimer();
    this.logManager.stop();
    this.ui.clearTransientMessages();
    this.ui.resetScrollPositions();
    this.lastInteraction = Date.now();
    this.subjectId = generateSubjectId();
    this.ui.showLabBadge(this.subjectId);
    this.ui.setRecRecording();
    this.logManager.startTicker("lab-log-ticker");
    this.logManager.startPopups("lab-popup");
    this.maze = new MazeGenerator(this.COLS, this.ROWS);
    this.player = new PlayerController(this.maze);
    this.revealed = new Set();
    this._revealCellAndNeighbors(0, 0);
    this.inputLocked = false;
    this.player.moving = false;
    this.ui.updateMission("宝箱を見つけよう");
    this.ui.setTreasureAcquired(false);
    this.ui.updateSteps(0);
    this.ui.updateTimer(0);
  };

  GameManager.prototype.startNewGame = async function() {
    if (this.inputLocked && $("screen-boot")?.classList.contains("active")) return;
    this.inputLocked = true;
    this.ui.clearTransientMessages();
    await this.ui.playBootSequence();
    await this.ui.playBriefingSequence();
    this._prepareGameSession();
    this.ui.showScreen("screen-game");
    this._resizeCanvases();
    this.player.startClock();
    this._startTimer();
    this._renderAll();
    if (!this.animHandle) this._loop();
  };

  GameManager.prototype._buildAndShowResult = async function() {
    const analysis = Analyzer.analyze(this.player);
    const record = {
      id: generateRecordId(), pid: this.subjectId, typeCode: analysis.typeCode,
      titleIndex: analysis.titleIndex, commentIndex: analysis.commentIndex,
      title: analysis.title, comment: analysis.comment, reasoning: analysis.reasoning,
      dfsScore: analysis.dfsScore, bfsScore: analysis.bfsScore, linearScore: analysis.linearScore,
      steps: analysis.stats.totalSteps, stepDiff: analysis.stats.stepDiff,
      explorationRate: analysis.stats.explorationRate, elapsedSeconds: analysis.stats.elapsedSeconds,
      gimmicks: analysis.gimmicks, timestamp: Date.now(),
    };
    this.lastRecord = record;
    const averages = await this.statistics.getAverageScores();
    await this.storage.saveResult(record);
    const aggregateStats = await this.statistics.getAggregateStats();
    this.resultRenderer.renderResult(record, this.maze, this.player, averages, aggregateStats);
    const cardUrl = QRManager.buildCardUrl(record);
    QRManager.renderInto($("qr-canvas-wrap"), $("qr-fallback-url"), cardUrl);
    this.ui.showScreen("screen-result");
  };

  GameManager.prototype.showTypeList = async function() {
    const stats = await this.statistics.getAggregateStats();
    this.resultRenderer.renderTypeList(stats);
    this.ui.showScreen("screen-type-list");
  };

  /* ================================================================
     Ver.1.7.2 final polish overrides
     -残すギミックをワープ/落とし穴に限定
     -エンディング入力仕様を「1回目で全文表示、2回目でタイトルへ」へ変更
  ================================================================ */
  EndingManager.prototype.play = function(subjectId, options = {}) {
    return new Promise((resolve) => {
      const fast = !!options.fast;
      const logEl = $("ending-log");
      const promptEl = $("ending-prompt");
      if (!logEl || !promptEl) { resolve(); return; }
      logEl.textContent = "";
      promptEl.classList.add("hidden");
      promptEl.innerHTML = "入力でもう一度表示 / 次の入力でタイトルへ<span class=\"ending-cursor\">▌</span>";
      const lines = [
        "━━━━━━━━━━━━━━",
        "Experiment Finished",
        "━━━━━━━━━━━━━━",
        "被験者No.", String(subjectId),
        "━━━━━━━━━━━━━━",
        "行動データ", "保存しました。",
        "━━━━━━━━━━━━━━",
        "ご協力ありがとうございました。",
        "━━━━━━━━━━━━━━",
        "STATUS", "COMPLETE",
        "━━━━━━━━━━━━━━",
      ];
      const fullText = lines.join("\n");
      const charDelay = fast ? 7 : 16;
      const linePause = fast ? 45 : 120;
      let lineIndex = 0, charIndex = 0, typing = true, complete = false, done = false;
      let timer = null, autoTimer = null;
      const cleanup = () => {
        if (timer) clearTimeout(timer);
        if (autoTimer) clearTimeout(autoTimer);
        window.removeEventListener("keydown", onKey, true);
        window.removeEventListener("pointerdown", onPointer, true);
      };
      const revealAll = () => {
        if (complete) return;
        if (timer) clearTimeout(timer);
        typing = false; complete = true;
        logEl.textContent = fullText;
        promptEl.textContent = "ENTER・SPACE・タップでタイトルへ戻る";
        promptEl.classList.remove("hidden");
      };
      const finish = () => {
        if (done) return;
        done = true; cleanup(); resolve();
      };
      const handleInput = (e) => {
        if (e && e.type === "keydown" && !(e.key === "Enter" || e.key === " " || e.code === "Space")) return;
        if (typing || !complete) { revealAll(); return; }
        finish();
      };
      function onKey(e){ handleInput(e); }
      function onPointer(e){ handleInput(e); }
      window.addEventListener("keydown", onKey, true);
      window.addEventListener("pointerdown", onPointer, true);
      autoTimer = setTimeout(() => { revealAll(); setTimeout(finish, fast ? 1200 : 2200); }, fast ? 4500 : 9000);
      const step = () => {
        if (done || complete) return;
        if (lineIndex >= lines.length) { revealAll(); return; }
        const line = lines[lineIndex];
        if (charIndex === 0 && logEl.textContent.length > 0) logEl.textContent += "\n";
        if (charIndex < line.length) {
          logEl.textContent += line[charIndex++];
          timer = setTimeout(step, charDelay);
        } else {
          lineIndex++; charIndex = 0;
          timer = setTimeout(step, linePause);
        }
      };
      step();
    });
  };

  // PlayerControllerの所持系プロパティは互換用に残しつつ、判定には使わない。
  PlayerController.prototype.tryMove = function(dir) {
    const noop = { moved: false, reachedGoal: false, treasureJustCollected: false, message: null };
    if (this.moving) return noop;
    const DIR_MAP = { up:{key:"N",dc:0,dr:-1}, down:{key:"S",dc:0,dr:1}, left:{key:"W",dc:-1,dr:0}, right:{key:"E",dc:1,dr:0} };
    const d = DIR_MAP[dir];
    if (!d) return noop;
    const cell = this.maze.cellAt(this.c, this.r);
    if (cell[d.key]) return noop;
    const from = { c:this.c, r:this.r };
    const to = { c:this.c+d.dc, r:this.r+d.dr };
    const gimmickType = this.maze.gimmickTypeAt(to.c, to.r);
    this._recordMove(from, to);
    this.c = to.c; this.r = to.r; this.moving = true;
    const treasureJustCollected = this.treasureCollected && this.treasureStepIndex === this.path.length - 1;
    let message = null;
    if (gimmickType === "pitfall") {
      this.pitfallHits++;
      message = "落とし穴に落ちた…スタート地点に戻される！";
      this._teleportTo(this.maze.start);
    } else if (gimmickType === "warpA" || gimmickType === "warpB") {
      this.warpUsed++;
      message = "ワープした！";
      this._teleportTo(this.maze.warpDestination(gimmickType));
    }
    const reachedGoal = this.c === this.maze.goal.c && this.r === this.maze.goal.r;
    return { moved:true, reachedGoal, treasureJustCollected, message };
  };

  // Analyzerから削除済みギミックの保存項目を除外し、危険回避判定を現行ギミックに合わせる。
  const originalAnalyze172 = Analyzer.analyze.bind(Analyzer);
  Analyzer.analyze = function(player) {
    const result = originalAnalyze172(player);
    result.gimmicks = {
      pitfallHits: player.pitfallHits || 0,
      warpUsed: player.warpUsed || 0,
    };
    if (result.typeCode === "R" && !result.reasoning.some((t)=>/危険|落とし穴|効率/.test(t))) {
      result.reasoning.push("落とし穴を避けながら効率よく任務を完了した");
    }
    return result;
  };

  // Ver.1.7.2: 結果画面の重複ボタンを研究資料メニューへ統合したため、旧IDは使わない。
  const originalRenderResult172 = ResultRenderer.prototype.renderResult;
  ResultRenderer.prototype.renderResult = function(record, maze, player, averages, aggregateStats) {
    originalRenderResult172.call(this, record, maze, player, averages, aggregateStats);
    const notice = $("warp-shortest-notice");
    if (notice) notice.classList.add("lab-status-notice");
  };

})();




/* ================================================================
   Ver.2.0 Release Candidate polish overrides
   研究レポートの視線誘導・AI資料・宝箱・リプレイ訴求を最終調整
================================================================ */
(function(){
  const byId = (id) => document.getElementById(id);
  const esc = (v) => String(v ?? "").replace(/[&<>"']/g, (ch) => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[ch]));
  const setText = (id, value) => { const el = byId(id); if (el) el.textContent = value; };
  const setHtml = (id, value) => { const el = byId(id); if (el) el.innerHTML = value; };

  const originalRenderResult20 = ResultRenderer.prototype.renderResult;
  ResultRenderer.prototype.renderResult = function(record, maze, player, averages, aggregateStats) {
    originalRenderResult20.call(this, record, maze, player, averages, aggregateStats);

    const total = Math.max(1, aggregateStats?.totalPlayers || 1);
    const count = (aggregateStats?.titleRanking || []).find((x) => x.title === record.title)?.count || 1;
    const rate = Math.round((count / total) * 1000) / 10;
    const ranking = [...(aggregateStats?.titleRanking || [])].sort((a,b)=>b.count-a.count);
    const rank = Math.max(1, ranking.findIndex((x) => x.title === record.title) + 1 || ranking.length + 1);
    setText("research-title-count", `現在 ${total}人中 ${count}名`);
    setText("research-title-rate", `${rate}% / 人気順位 ${rank}位`);

    const proposalPool = [];
    if (record.typeCode === "D") proposalPool.push("次は近い道から順番に確認すると、効率派の称号が出るかもしれません。");
    if (record.typeCode === "B") proposalPool.push("次はあえて寄り道すると、探究者タイプのデータが取れる可能性があります。");
    if (record.typeCode === "L") proposalPool.push("次は直感で進むと、別の探索パターンとして記録されるかもしれません。");
    if ((record.gimmicks?.warpUsed || 0) === 0) proposalPool.push("転送装置を使うルートを試すと、理論最短が変わる場合があります。");
    if ((record.gimmicks?.pitfallHits || 0) === 0) proposalPool.push("怪しい床を見抜けました。次はスピード重視の探索も観測してみたいです。");
    proposalPool.push("未知の探索パターンが、まだ発見されていません。別ルートで再実験できます。");
    setText("replay-suggestion", pickRandom(proposalPool));

    const report = byId("screen-result");
    if (report) report.classList.add("release-report-mode");
  };

  ResultRenderer.prototype.renderExplainPersonal = function(record) {
    setText("explain-your-title", record.title);
    setHtml("explain-reasons", (record.reasoning || []).map((reason) => `<li>${esc(reason)}</li>`).join(""));
    const top = [
      ["DFS", record.dfsScore, "奥へ進む・行き止まりまで確かめる動きが強いほど上がります。"],
      ["BFS", record.bfsScore, "少ない歩数で近い場所から確認できるほど上がります。"],
      ["線形探索", record.linearScore, "順番を決めて一つずつ確認する動きが強いほど上がります。"],
    ];
    const strongest = top.slice().sort((a,b)=>b[1]-a[1])[0];
    const dataLine = `今回のプレイでは、${strongest[0]}の特徴が一番強く出ました。歩数は${record.steps}、最短との差は${record.stepDiff >= 0 ? "+" : ""}${record.stepDiff}、探索率は${record.explorationRate}%です。`;
    setHtml("explain-score-links", `
      <div class="personal-data-card">
        <p class="eyebrow">YOUR PLAY DATA</p>
        <p>${esc(dataLine)}</p>
        <div class="personal-score-grid">
          ${top.map(([name, score, note]) => `<div><b>${esc(name)}</b><span>${score}%</span><small>${esc(note)}</small></div>`).join("")}
        </div>
        <p class="howto-hint">ゲーム中の移動ログを、DFS・BFS・線形探索の考え方に照らし合わせています。難しい言葉に見えても、要するに「どんな探し方をしたか」の分類です。</p>
      </div>
    `);
  };

  // マップ上の宝箱スプライト。CSSではなくCanvas描画を直接更新する。
  // 16×16基準の少ないドットで、未取得/取得済みを一目で判別できるポップな8bit宝箱にする。
  Renderer._drawTreasure = function(ctx, x, y, cellPx, opened = false) {
    const u = cellPx / 16;
    const px = (n) => Math.round(n * u);
    const ox = x + px(2);
    const oy = y + px(3);
    const R = (gx, gy, gw, gh, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(ox + px(gx), oy + px(gy), Math.max(1, px(gw)), Math.max(1, px(gh)));
    };

    ctx.save();
    ctx.imageSmoothingEnabled = false;

    // 足元の小さな影。判定・サイズは変えず、見た目だけを少し浮かせる。
    ctx.shadowBlur = 0;
    ctx.fillStyle = opened ? "rgba(77,238,234,0.08)" : "rgba(255,206,84,0.12)";
    ctx.fillRect(x + px(4), y + px(12), px(8), px(2));

    if (!opened) {
      // 取得前：丸みのある木箱＋金具＋鍵穴。少ないドットで宝箱らしさを優先。
      ctx.shadowColor = "rgba(255,206,84,0.55)";
      ctx.shadowBlur = Math.max(3, cellPx * 0.12);
      R(1, 4, 12, 8, "#2a160c"); // outline
      ctx.shadowBlur = 0;

      // lid / body
      R(2, 4, 10, 1, "#5a2b16");
      R(1, 5, 12, 3, "#9b5525");
      R(2, 5, 10, 1, "#d57932");
      R(2, 7, 10, 1, "#663119");
      R(1, 8, 12, 4, "#7a3d1d");
      R(2, 8, 10, 1, "#b8642d");
      R(2, 11, 10, 1, "#3a1d10");

      // chunky gold bands
      R(1, 8, 12, 1, "#ffcf4a");
      R(1, 5, 2, 7, "#e7a93a");
      R(11, 5, 2, 7, "#e7a93a");
      R(2, 5, 1, 1, "#fff0a6");
      R(11, 5, 1, 1, "#fff0a6");

      // center lock plate and keyhole
      R(5, 8, 4, 3, "#ffd95a");
      R(6, 9, 2, 2, "#05070d");
      R(7, 10, 1, 1, "#05070d");

      // tiny sparkle kept inside the tile so it does not affect collision/placement
      R(13, 2, 1, 1, "#fff4b8");
      R(12, 3, 3, 1, "#ffcf4a");
      R(13, 4, 1, 1, "#fff4b8");
      R(0, 3, 1, 1, "#fff4b8");
    } else {
      // 取得済み：壊れた箱ではなく、フタが開いた空っぽの宝箱。
      ctx.shadowColor = "rgba(77,238,234,0.25)";
      ctx.shadowBlur = Math.max(2, cellPx * 0.08);
      R(1, 2, 12, 4, "#2a160c"); // open lid outline
      R(1, 8, 12, 4, "#2a160c"); // base outline
      ctx.shadowBlur = 0;

      // opened lid behind the base
      R(2, 2, 10, 1, "#5a2b16");
      R(1, 3, 12, 3, "#8e4a22");
      R(2, 3, 10, 1, "#c86d30");
      R(2, 5, 10, 1, "#4b2413");
      R(1, 6, 12, 1, "#ffcf4a");

      // empty dark interior clearly visible
      R(3, 6, 8, 2, "#15080a");
      R(4, 7, 6, 1, "#2b120d");

      // base chest, still intact
      R(1, 8, 12, 4, "#7a3d1d");
      R(2, 8, 10, 1, "#b8642d");
      R(2, 11, 10, 1, "#3a1d10");
      R(1, 8, 12, 1, "#ffcf4a");
      R(1, 8, 2, 4, "#e7a93a");
      R(11, 8, 2, 4, "#e7a93a");
      R(5, 9, 4, 2, "#ffd95a");
      R(6, 10, 2, 1, "#05070d");

      // small cyan glint meaning “collected”, not a broken mark
      R(12, 3, 1, 1, "#9ffcff");
      R(13, 4, 1, 1, "#4deeea");
    }
    ctx.restore();
  };
})();



/* ================================================================
   Ver.2.0 RC Final polish overrides
   - ワープ解析通知をアイコン/タイトル/本文に分離
   - 適性バーと数値を1秒前後で同期アニメーション
   - 研究評価の星を順番に点灯
================================================================ */
(() => {
  const $ = (id) => document.getElementById(id);
  const esc = (v) => String(v ?? "").replace(/[&<>"']/g, (ch) => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[ch]));

  ResultRenderer.prototype._animateBar = function(barId, pctId, value) {
    const bar = $(barId);
    const pct = $(pctId);
    const target = Math.max(0, Math.min(100, Math.round(Number(value) || 0)));
    const duration = 1000;
    const start = performance.now();
    if (bar) {
      bar.style.width = "0%";
      bar.style.transition = "none";
      // 強制リフローで毎回0%から気持ちよく伸ばす
      void bar.offsetWidth;
      bar.style.transition = "width 1s cubic-bezier(.16, 1, .3, 1)";
      requestAnimationFrame(() => { bar.style.width = target + "%"; });
    }
    const easeOutCubic = (t) => 1 - Math.pow(1 - t, 3);
    const tick = (now) => {
      const t = Math.min(1, (now - start) / duration);
      const current = Math.round(target * easeOutCubic(t));
      if (pct) pct.textContent = current + "%";
      if (t < 1) requestAnimationFrame(tick);
    };
    requestAnimationFrame(tick);
  };

  function buildLabNotice(title, body) {
    return `
      <span class="lab-alert-icon" aria-hidden="true">ⓘ</span>
      <span class="lab-alert-title">${esc(title)}</span>
      <span class="lab-alert-body">${esc(body)}</span>
    `;
  }

  function animateStars(el, starsText) {
    if (!el) return;
    const onCount = (starsText.match(/★/g) || []).length;
    el.innerHTML = `<span class="eval-stars" aria-label="${esc(starsText)}">${Array.from({ length: 5 }, (_, i) => `<span class="star${i < onCount ? " target" : ""}">★</span>`).join("")}</span>`;
    const stars = Array.from(el.querySelectorAll(".star.target"));
    stars.forEach((star, i) => {
      setTimeout(() => star.classList.add("on"), 120 + i * 120);
    });
  }

  const previousRenderResultFinal = ResultRenderer.prototype.renderResult;
  ResultRenderer.prototype.renderResult = function(record, maze, player, averages, aggregateStats) {
    previousRenderResultFinal.call(this, record, maze, player, averages, aggregateStats);

    const notice = $("warp-shortest-notice");
    if (notice) {
      notice.className = "route-notice lab-alert";
      const normal = typeof normalMissionPath === "function" ? normalMissionPath(maze) : [];
      const gimmick = typeof gimmickMissionPath === "function" ? gimmickMissionPath(maze) : [];
      const normalSteps = typeof pathSteps === "function" ? pathSteps(normal) : 0;
      const gimmickSteps = typeof pathSteps === "function" ? pathSteps(gimmick) : 0;
      let body = "このマップでは通常経路が理論最短として採用されました。";
      if ((record.gimmicks?.warpUsed || 0) > 0) {
        body = "ワープ使用により、あなたの探索ルートに転送行動が記録されました。";
      } else if (gimmickSteps < normalSteps) {
        body = "このマップでは、転送装置を使うと理論最短が短くなる可能性があります。";
      }
      notice.innerHTML = buildLabNotice("解析ステータス", body);
    }

    const evalQuality = $("eval-quality");
    if (evalQuality) animateStars(evalQuality, evalQuality.textContent || "★★★☆☆");
  };
})();

/* ================================================================
   初期化処理
================================================================ */
window.addEventListener("DOMContentLoaded", async () => {
  const game = new GameManager();
  game.init();

  // QRコード経由でアクセスされた場合は、SYSTEM BOOT演出を飛ばして
  // 診断カード画面を直接表示する（スキャンした人を待たせないため）
  const shownCard = await game.tryShowCardFromUrl();
  if (shownCard) return;

  // Ver.1.7: SYSTEM BOOTはSTART後に毎回表示する。初期表示はすぐタイトルへ。
  game.ui.showScreen("screen-title");
});

/* ================================================================
   Final map pitfall icon override
   - 変更対象はマップ上の落とし穴アイコンのみ
   - Canvas描画の最終上書きなので、実際のゲーム画面に反映される
   - 判定・位置・迷路生成・ワープ・宝箱・ゴールは変更しない
================================================================ */
(() => {
  const readCssColor = (name, fallback) => {
    const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    return v || fallback;
  };

  Renderer._drawPitfall = function(ctx, x, y, cellPx) {
    const u = cellPx / 16;
    const px = (n) => Math.round(n * u);
    const R = (gx, gy, gw, gh, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(
        x + px(gx),
        y + px(gy),
        Math.max(1, px(gw)),
        Math.max(1, px(gh))
      );
    };

    const cyan = readCssColor("--pitfall-rim", "#4deeea");
    const pink = readCssColor("--pitfall-warning", "#ff2e6d");
    const glow = readCssColor("--pitfall-shadow", "rgba(77,238,234,0.55)");

    ctx.save();
    ctx.imageSmoothingEnabled = false;

    // 研究所の床パネルに「回収ゲート」が開いたデザイン。
    // 前回の黒い穴・渦デザインから変えて、床タイル＋警告ライン中心にする。
    ctx.shadowColor = glow;
    ctx.shadowBlur = Math.max(4, cellPx * 0.14);
    R(3, 3, 10, 10, "rgba(77,238,234,0.09)");
    R(4, 4, 8, 8, "rgba(255,46,109,0.07)");
    ctx.shadowBlur = 0;

    // 外枠：ラボの床パネル感を残す。
    R(4, 2, 8, 1, "#2d3f6f");
    R(3, 3, 10, 1, "#1a2d58");
    R(2, 4, 12, 2, "#112345");
    R(2, 6, 12, 5, "#0c1935");
    R(3, 11, 10, 2, "#112345");
    R(4, 13, 8, 1, "#1a2d58");

    // 中央：落下口ではなく、スタートへ戻す転送ゲート風のスリット。
    R(5, 5, 6, 1, "#263a72");
    R(4, 6, 8, 1, "#101c45");
    R(4, 7, 8, 2, "#050814");
    R(5, 9, 6, 1, "#0a1230");
    R(6, 10, 4, 1, "#02040b");

    // 上下の警告バー。小さくても罠マスと分かるようにする。
    R(5, 4, 1, 1, pink);
    R(6, 4, 1, 1, "#ffd166");
    R(7, 4, 1, 1, pink);
    R(8, 4, 1, 1, "#ffd166");
    R(9, 4, 1, 1, pink);
    R(10, 4, 1, 1, "#ffd166");
    R(5, 11, 1, 1, "#ffd166");
    R(6, 11, 1, 1, pink);
    R(7, 11, 1, 1, "#ffd166");
    R(8, 11, 1, 1, pink);
    R(9, 11, 1, 1, "#ffd166");
    R(10, 11, 1, 1, pink);

    // シアンの角マーカー。既存UIの雰囲気に合わせる。
    R(4, 3, 2, 1, cyan);
    R(10, 3, 2, 1, cyan);
    R(3, 4, 1, 2, cyan);
    R(12, 4, 1, 2, cyan);
    R(3, 10, 1, 2, cyan);
    R(12, 10, 1, 2, cyan);
    R(4, 12, 2, 1, cyan);
    R(10, 12, 2, 1, cyan);

    // 「戻される」ニュアンスの下向き矢印。ネタバレしすぎない程度の抽象記号。
    R(7, 5, 2, 1, "#e4d4ff");
    R(7, 6, 2, 1, cyan);
    R(6, 7, 4, 1, "#8a56ff");
    R(7, 8, 2, 1, cyan);
    R(6, 9, 1, 1, "#b991ff");
    R(7, 9, 2, 1, "#b991ff");
    R(9, 9, 1, 1, "#b991ff");

    // 床の割れ目とデータ欠片。ポップなドット絵感だけ残す。
    R(2, 3, 1, 1, "#314574");
    R(13, 3, 1, 1, "#314574");
    R(4, 6, 1, 1, "#26346d");
    R(11, 6, 1, 1, "#26346d");
    R(5, 13, 1, 1, pink);
    R(11, 13, 1, 1, "#bfffff");
    R(1, 8, 2, 1, cyan);
    R(13, 8, 2, 1, "#8a56ff");

    // 小さな白ハイライト。
    R(4, 4, 1, 1, "#ffffff");
    ctx.restore();
  };
})();
