'use strict';
/* ドランカー オンライン対戦サーバー（外部ライブラリ不要。Node.js 18以上）
   ルール判定・配札・手札の秘匿はすべてここで行い、各プレイヤーには見てよい情報だけを送ります。 */
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const PORT=process.env.PORT||3000,GUID='258EAFA5-E914-47DA-95CA-C5AB0DC85B11',rooms=new Map(),conns=new Set();

/* ---------- ルール（CPU版のresolveTurn等を、2人の人間用に移植） ---------- */
const SU={S:'♠',C:'♣',H:'♥',D:'♦'},RK=r=>({14:'A',13:'K',12:'Q',11:'J'}[r]||String(r)),lab=c=>RK(c.r)+SU[c.s];
const cmp=(x,y)=>x.r===2&&y.r===14?1:x.r===14&&y.r===2?-1:Math.sign(x.r-y.r);
const shuffle=a=>{for(let i=a.length-1;i>0;i--){const j=crypto.randomInt(i+1);[a[i],a[j]]=[a[j],a[i]]}return a};
const canShot=(S,p)=>!S.su[p]&&!S.so,N=s=>`{${s}}`; // {0}{1}は席番号。送信時に名前へ置き換える

function newGame(R,first){const d=[];let id=0;for(const s of'SCHD')for(let r=2;r<=14;r++)d.push({id:id++,r,s});
  R.S={phase:'x',deck:shuffle(d),disc:[],g:[0,0],su:[false,false],so:false,first,round:0,log:[]};startRound(R)}

function startRound(R){const S=R.S;S.round++;
  if(S.deck.length<8){S.deck=shuffle(S.deck.concat(S.disc));S.disc=[];S.log.push('山札を切り直した')}
  S.hand=[S.deck.splice(0,4),S.deck.splice(0,4)];S.rev=[new Set,new Set];S.sg=S.g.slice();
  S.off=S.sg.map(x=>x>=15);S.need=S.sg.map(x=>x>=10?2:x>=5?1:0);
  S.pr=[S.need[0]?null:[],S.need[1]?null:[]];S.draws=0;S.turns=0;S.parent=S.first;S.fixed=false;S.rm=null;
  S.log.push(`── ラウンド${S.round}（最初の親：${N(S.parent)}）`);
  if(S.need[0]||S.need[1])S.phase='reveal';else beginTurn(R)}

function doReveal(R,p,ids){const S=R.S;
  if(S.phase!=='reveal'||!S.need[p]||S.pr[p]||!Array.isArray(ids)||ids.length!==S.need[p]||new Set(ids).size!==ids.length||!ids.every(i=>S.hand[p].some(c=>c.id===i)))return;
  S.pr[p]=ids;
  if(S.pr[0]&&S.pr[1]){for(const q of[0,1]){S.rev[q]=new Set(S.pr[q]);if(S.need[q])S.log.push(`${N(q)}が${S.need[q]}枚公開：${S.hand[q].filter(c=>S.rev[q].has(c.id)).map(lab).join(' ')}`)}beginTurn(R)}}

function beginTurn(R){const S=R.S;S.phase='play';S.played=[null,null];S.res=null;S.pend=null;S.sd=[null,null];S.ready=[false,false]}

function play(R,p,id){const S=R.S;if(S.phase!=='play'||S.played[p]||(p!==S.parent&&!S.played[S.parent]))return;
  const i=S.hand[p].findIndex(c=>c.id===id);if(i<0)return;S.played[p]=S.hand[p].splice(i,1)[0];
  if(S.played[0]&&S.played[1]){S.phase='shot';S.sd=[0,1].map(q=>canShot(S,q)?null:false);if(S.sd.every(x=>x!==null))resolve(R)}}

function shot(R,p,use){const S=R.S;if(S.phase!=='shot'||S.sd[p]!==null)return;S.sd[p]=!!use;if(S.sd.every(x=>x!==null))resolve(R)}

function resolve(R){const S=R.S,c=S.played,d=[0,0],L=[];
  let w=cmp(c[0],c[1]);w=w>0?0:w<0?1:null;
  if(w!==null){const l=1-w;if(!S.off[l]&&c[l].s==='C'&&c[l].r*2<c[w].r){L.push(`${N(l)}の乱闘！ 引き分け扱いに`);w=null}}
  if(w!==null){const l=1-w;d[l]+=c[l].r>>1;if(!S.off[w]&&c[w].s==='S'){d[l]++;L.push(`${N(w)}の蒸留酒：+1`)}}
  for(const p of[0,1])if(S.sd[p]){S.su[p]=true;const v=c[1-p].r>>1;d[1-p]+=v;L.push(`${N(p)}のショット！ ${N(1-p)}に+${v}`)}
  S.g[0]+=d[0];S.g[1]+=d[1];
  if(w!==null&&!S.off[w]&&c[w].s==='H'){const h=Math.max(1,c[w].r>>2);S.g[w]=Math.max(0,S.g[w]-h);L.push(`${N(w)}の介抱：-${h}`)}
  S.disc.push(c[0],c[1]);
  let next;
  if(S.g[0]>=20&&S.g[1]>=20){next='rdraw';S.so=true;L.push('両者が20超過：ラウンド引き分け・以降ショット無効')}
  else if(S.g[0]>=20||S.g[1]>=20)next='over';
  else if(w===null){S.draws++;next=S.draws>=3?'rdraw':'cont';if(next==='rdraw')L.push('引き分け3回：ラウンド引き分け')}
  else{S.turns++;next=S.turns>=2?'rend':'cont'}
  let ck=null;
  if(next==='cont'){const cand=[S.parent,1-S.parent].filter(p=>!S.off[p]&&c[p].s==='D'&&(w===p||w===null));if(cand.length)ck=cand[0]}
  S.pend=ck;S.res={w,d,L,next,c:[c[0],c[1]]};S.phase='result';S.ready=[false,false];if(ck===null)auto(R);
  S.log.push(`${lab(c[0])}（${N(0)}） vs ${lab(c[1])}（${N(1)}） → ${w===null?'引き分け':N(w)+'の勝ち'}`,...L)}

const AUTO_MS=4000; // 結果を見せてから自動で進むまでの時間
function auto(R){const k=R.k=(R.k||0)+1;setTimeout(()=>{if(R.k===k&&rooms.get(R.code)===R&&R.S.phase==='result'&&R.S.pend===null){advance(R);bcast(R)}},AUTO_MS)}
function setParent(R,p,who){const S=R.S;S.parent=who==='me'?p:1-p;S.fixed=true;S.pend=null;
  const t=`${N(p)}のカクテル：${N(S.parent)}が親に固定`;S.log.push(t);S.res.L.push(`${N(S.parent)}が親に固定`);auto(R)}

function advance(R){const S=R.S,r=S.res;
  if(r.next==='cont'){if(!S.fixed&&r.w!==null)S.parent=1-S.parent;beginTurn(R)}
  else if(r.next==='rend')endRound(R);
  else if(r.next==='rdraw'){S.g=S.sg.slice();S.log.push('酩酊ゲージをラウンド開始前に戻した');endRound(R)}
  else S.phase='over'}
function endRound(R){const S=R.S;S.disc.push(...S.hand[0],...S.hand[1]);startRound(R)}

/* ---------- 各プレイヤーに見せてよい情報だけを作る（添字は0＝自分、1＝相手に変換） ---------- */
function view(R,p){const S=R.S,q=1-p,o=R.seats[q],rel=s=>s===null?null:s===p?0:1,
  sub=t=>t.replace(/\{(\d)\}/g,(_,s)=>+s===p?'あなた':R.seats[+s].name),
  v={t:'state',room:R.code,you:p,opp:o?o.name:'',oc:!!(o&&o.c),phase:S.phase};
  if(S.round)Object.assign(v,{round:S.round,turns:S.turns,draws:S.draws,deck:S.deck.length,
    g:[S.g[p],S.g[q]],sg:[S.sg[p],S.sg[q]],su:[S.su[p],S.su[q]],so:S.so,off:[S.off[p],S.off[q]],need:[S.need[p],S.need[q]],parent:rel(S.parent),
    hand:S.hand[p],rev:[...S.rev[p]],oh:S.hand[q].map(c=>S.rev[q].has(c.id)?c:null), // 相手の伏せ札はnull
    pd:[!!S.pr[p],!!S.pr[q]],sd:S.sd?[S.sd[p]!==null,S.sd[q]!==null]:[false,false],
    pl:[S.played?S.played[p]:null,S.played&&S.played[q]?((S.phase==='result'||S.rev[q].has(S.played[q].id))?S.played[q]:{}):null],
    res:S.res&&{w:rel(S.res.w),d:[S.res.d[p],S.res.d[q]],L:S.res.L.map(sub),next:S.res.next,c:[S.res.c[p],S.res.c[q]]},
    pend:rel(S.pend),rd:S.ready?[S.ready[p],S.ready[q]]:[false,false],rm:S.rm?[S.rm[p],S.rm[q]]:[false,false],log:S.log.slice(-40).map(sub)});
  return v}

/* ---------- 部屋と通信 ---------- */
const send=(c,o)=>{const p=Buffer.from(JSON.stringify(o)),n=p.length;let h;
  if(n<126)h=Buffer.from([0x81,n]);else if(n<65536){h=Buffer.alloc(4);h[0]=0x81;h[1]=126;h.writeUInt16BE(n,2)}else{h=Buffer.alloc(10);h[0]=0x81;h[1]=127;h.writeBigUInt64BE(BigInt(n),2)}
  if(!c.sock.destroyed)c.sock.write(Buffer.concat([h,p]))};
const ctl=(s,op,p=Buffer.alloc(0))=>{if(!s.destroyed)s.write(Buffer.concat([Buffer.from([128|op,p.length]),p]))};
const bcast=R=>R.seats.forEach((s,p)=>s&&s.c&&send(s.c,view(R,p)));
const err=(c,msg,fatal)=>send(c,{t:'err',msg,fatal:fatal?1:0});
const code=()=>{let s;do{s=Array.from({length:5},()=>'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'[crypto.randomInt(32)]).join('')}while(rooms.has(s));return s};
const mkSeat=n=>({name:String(n||'').replace(/[\u0000-\u001f<>&"']/g,'').trim().slice(0,10)||'プレイヤー',token:crypto.randomBytes(12).toString('hex'),c:null});
function attach(c,R,p){c.R=R;c.p=p;R.seats[p].c=c;R.t=Date.now();send(c,{t:'joined',room:R.code,token:R.seats[p].token,you:p});bcast(R)}

function onMsg(c,m){if(!m||typeof m!=='object')return;const t=m.t;
  if(t==='create'){if(c.R||rooms.size>300)return;const R={code:code(),seats:[mkSeat(m.name),null],S:{phase:'lobby',log:[]},t:Date.now()};rooms.set(R.code,R);return attach(c,R,0)}
  if(t==='join'){if(c.R)return;const R=rooms.get(String(m.room||'').toUpperCase());
    if(!R||R.seats[1])return err(c,'部屋が見つからないか、すでに満員です');R.seats[1]=mkSeat(m.name);R.S.phase='choose';return attach(c,R,1)}
  if(t==='rejoin'){const R=rooms.get(String(m.room||'')),p=R?R.seats.findIndex(s=>s&&s.token===m.token):-1;
    if(p<0)return err(c,'部屋が見つかりません（閉じられた可能性があります）',1);
    const old=R.seats[p].c;R.seats[p].c=c;if(old&&old!==c)old.sock.destroy();return attach(c,R,p)}
  const R=c.R,p=c.p;if(!R)return;R.t=Date.now();const S=R.S;
  if(t==='leave'){rooms.delete(R.code);R.seats.forEach((s,i)=>{if(s&&s.c){s.c.R=null;if(i!==p)err(s.c,'相手が退出したため部屋が閉じられました',1)}});return}
  if(t==='start'&&p===0&&S.phase==='choose')newGame(R,m.who==='child'?1:0);
  else if(t==='reveal')doReveal(R,p,m.ids);
  else if(t==='play')play(R,p,m.id);
  else if(t==='shot')shot(R,p,m.use);
  else if(t==='parent'&&S.phase==='result'&&S.pend===p)setParent(R,p,m.who);
  else if(t==='rematch'&&S.phase==='over'){S.rm=S.rm||[false,false];S.rm[p]=true;if(S.rm[0]&&S.rm[1])newGame(R,1-S.first)}
  bcast(R)}

/* ---------- HTTPとWebSocket（RFC6455の最小実装） ---------- */
const srv=http.createServer((req,res)=>{const u=req.url.split('?')[0];
  if(u==='/'||u==='/index.html')fs.readFile(path.join(__dirname,'index.html'),(e,d)=>{res.writeHead(e?500:200,{'Content-Type':'text/html; charset=utf-8','Cache-Control':'no-cache'});res.end(e?'index.html not found':d)});
  else if(u==='/healthz'){res.writeHead(200);res.end('ok')}else{res.writeHead(404);res.end('not found')}});

function pump(c){for(;;){const b=c.buf;if(b.length<2)return;let n=b[1]&127,o=2;
  if(!(b[1]&128)||n===127)return c.sock.destroy();
  if(n===126){if(b.length<4)return;n=b.readUInt16BE(2);o=4}
  if(n>8192)return c.sock.destroy();if(b.length<o+4+n)return;
  const k=b.subarray(o,o+4),p=Buffer.from(b.subarray(o+4,o+4+n));for(let i=0;i<n;i++)p[i]^=k[i&3];
  c.buf=b.subarray(o+4+n);const op=b[0]&15,fin=b[0]&128;
  if(op===8){c.sock.end(Buffer.from([0x88,0]));return}
  if(op===9){ctl(c.sock,10,p.subarray(0,125));continue}
  if(op===10){c.alive=true;continue}
  c.frag.push(p);if(c.frag.length>4)return c.sock.destroy();if(!fin)continue;
  const s=Buffer.concat(c.frag).toString();c.frag=[];if(++c.n>60)return c.sock.destroy();
  let m;try{m=JSON.parse(s)}catch(e){continue}onMsg(c,m)}}

srv.on('upgrade',(req,sock)=>{const k=req.headers['sec-websocket-key'],o=req.headers.origin;
  try{if(!k||(o&&new URL(o).host!==req.headers.host))return sock.destroy()}catch(e){return sock.destroy()}
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: '+crypto.createHash('sha1').update(k+GUID).digest('base64')+'\r\n\r\n');
  const c={sock,buf:Buffer.alloc(0),frag:[],alive:true,n:0,R:null,p:0};conns.add(c);
  sock.on('data',d=>{c.buf=Buffer.concat([c.buf,d]);pump(c)});
  sock.on('error',()=>{});
  sock.on('close',()=>{conns.delete(c);const R=c.R;if(R&&R.seats[c.p]&&R.seats[c.p].c===c){R.seats[c.p].c=null;bcast(R)}})});

setInterval(()=>{for(const c of conns){if(!c.alive){c.sock.destroy();continue}c.alive=false;ctl(c.sock,9)}},25000); // 接続維持＋切断検知
setInterval(()=>{for(const c of conns)c.n=0},10000); // 連打対策
setInterval(()=>{for(const[k,R]of rooms)if(!R.seats.some(s=>s&&s.c)&&Date.now()-R.t>30*60000)rooms.delete(k)},5*60000); // 放置された部屋を削除
srv.listen(PORT,'0.0.0.0',()=>console.log('ドランカー起動: http://localhost:'+PORT));
