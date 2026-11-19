(() => {
  'use strict';
  const data = window.CAMERA_MAP_DATA;
  const routeData = window.CAMERA_ROUTE_DATA;
  const allBuildings = data.buildings.slice().sort((a,b)=>a.order-b.order);
  const buildings = allBuildings.filter(b=>routeData.modes.together.order.includes(b.id));
  const byId = new Map(allBuildings.map(b=>[b.id,b]));
  const rooms = window.CAMERA_ROOM_DATA.rooms.slice().sort((a,b)=>a.key-b.key);
  const roomById = new Map(rooms.map(room=>[room.id,room]));
  const keyCatalog = window.CAMERA_KEY_CATALOG.keys;
  const keyById = new Map(keyCatalog.map(key=>[key.id,key]));
  const pointRules = window.CAMERA_POINT_RULES;
  const rulesByType = new Map(pointRules.types.map(rule=>[rule.typeId,rule]));
  const NS = 'http://www.w3.org/2000/svg';
  const $ = id => document.getElementById(id);
  const svg = $('map');
  const groups = {route:$('route-lines'),shapes:$('building-shapes'),buildings:$('building-markers'),leaders:$('target-leaders'),doors:$('door-markers'),targets:$('target-markers'),computers:$('computer-markers'),trash:$('trash-markers')};
  const colors = {furniture:'#16875d',drill:'#7750b1',small:'#ac6b04',deposit:'#3c6e97',computer:'#17668d',atm:'#575fac'};
  const colorLight = {furniture:'#37ba89',drill:'#be9bff',small:'#efbc57',deposit:'#7cbce9',computer:'#7dd4ec',atm:'#b7b9ff'};
  const routeColors={A:'#823bb6',B:'#087fa1',link:'#64707b'};
  const coarse = window.matchMedia('(pointer: coarse)').matches;
  const reduceMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  let selected = null, floorLevel = 0, selectedTarget = null;
  let routeMode='split', includeDrills=true;
  let viewMode=location.hash==='#plantes'?'plants':location.hash==='#poubelles'?'trash':'doors', selectedRoom=null, selectedKeyId=null, searchQuery='', districtFilter='all';
  const trashData=window.TRASH_MAP_DATA;
  const trashPoints=trashData.points.map(point=>{
    const nearest=allBuildings.reduce((best,b)=>{const f=b.floors[0],x=f?(f.bounds[0]+f.bounds[2])/2:b.x,y=f?(f.bounds[1]+f.bounds[3])/2:-b.z,distance=Math.hypot(point.x-x,point.y-y);return !best||distance<best.distance?{b,distance}:best;},null);
    return {...point,nearby:nearest.b.name};
  });
  let trashQuery='';
  const plantData=window.PLANT_SEARCH_DATA;
  let plantSaved={},plantStorage=true;
  try{plantSaved=JSON.parse(localStorage.getItem('rob-run-plants-v2')||'{}')||{};}catch{plantStorage=false;}
  let plantSector=plantSaved.revision===plantData.revision&&Object.hasOwn(plantData.sectors,plantSaved.sector)?plantSaved.sector:'all',plantExtra=plantSaved.extra===true,plantSelected=null;
  const plantDone=new Set((Array.isArray(plantSaved.done)?plantSaved.done:[]).filter(id=>Object.hasOwn(plantData.stops,id)));
  const plantOrder=()=>Object.keys(plantData.stops).filter(id=>!plantData.sectors[plantSector].district||plantData.stops[id].district===plantData.sectors[plantSector].district);
  function plantRouteOrder(){
    const order=plantOrder().filter(id=>plantExtra||plantData.stops[id].routeEligible).sort((a,b)=>plantData.buildingOrder.indexOf(plantData.stops[a].buildingId)-plantData.buildingOrder.indexOf(plantData.stops[b].buildingId));
    const first=order.findIndex(id=>plantData.stops[id].buildingId===plantData.routeStart);
    return first>0?[...order.slice(first),...order.slice(0,first)]:order;
  }
  const plantName=p=>p.title||byId.get(p.buildingId).name;
  const nextPlant=()=>plantRouteOrder().find(id=>!plantDone.has(id));
  function savePlants(){try{localStorage.setItem('rob-run-plants-v2',JSON.stringify({revision:plantData.revision,sector:plantSector,extra:plantExtra,done:[...plantDone]}));}catch{plantStorage=false;}}
  const defaultLayers={purple:true,gold:false,otherKeys:false,furniture:true,drill:true,small:true,computers:true,deposit:false,route:false,labels:true,loot:false,security:false,atm:false,trash:false};
  let preferences={};try{preferences=JSON.parse(localStorage.getItem('rob-run-atlas-v1')||'{}');}catch{}
  const layers={...defaultLayers,...Object.fromEntries(Object.entries(preferences.layers||{}).filter(([key,value])=>key in defaultLayers&&typeof value==='boolean'))};
  if(viewMode==='trash')layers.trash=true;
  const hiddenKeyIds=new Set(preferences.hiddenKeys||[]),hiddenBuildingIds=new Set(preferences.hiddenBuildings||[]);
  let view={x:-480,y:-200,w:1000,h:550};
  let animation=0, drawFrame=0, animationTarget=null;
  const pointers=new Map();
  let gesture=null, clickSuppressed=false;

  function el(tag, attrs={}, text='') {
    const n=document.createElementNS(NS,tag);
    for(const [k,v] of Object.entries(attrs))n.setAttribute(k,String(v));
    if(text)n.textContent=text;
    return n;
  }
  const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const isPharmacy=b=>b.id==='Pharmacy_01'||b.id==='Pharmacy_02';
  const owner=b=>b.district==='Downtown'?'A':'B';
  const inPlan=(b,t)=>t.kind==='furniture'||(includeDrills&&t.kind==='drill'&&!isPharmacy(b));
  const gain=t=>Number.isFinite(t.points)?t.points:null;
  const gainBadge=t=>gain(t)===null?'?':`+${gain(t)}`;
  const sumPoints=targets=>targets.reduce((sum,t)=>sum+(gain(t)||0),0);
  const planPoints=b=>sumPoints(b.floors.flatMap(f=>f.targets).filter(t=>inPlan(b,t)));
  const floorPoints=(b,f)=>sumPoints(f.targets.filter(t=>inPlan(b,t)));
  const plannedDrills=b=>includeDrills&&!isPharmacy(b)?b.drillCount:0;
  const normalize=s=>String(s||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase();
  const keyName=id=>keyById.get(id)?.displayNameFr||(id?.startsWith('safe_key')?'Clé de coffre':'Clé de pièce');
  const keyPlace=id=>keyById.get(id)?.locationLabelFr||keyById.get(id)?.aliasFr||'';
  const keyDescription=id=>keyById.get(id)?.descriptionFr||'';
  const keyIcon=id=>keyById.get(id)?.icon||'';
  const keyLayer=key=>key.family==='safe_key'||key.id.startsWith('safe_key_')?'small':key.id.startsWith('room_key_')?(key.rarity==='epic'?'purple':'gold'):'otherKeys';
  const matchesText=text=>normalize(searchQuery).trim().split(/\s+/).filter(Boolean).every(word=>normalize(text).includes(word));
  const matchesKey=key=>!searchQuery||matchesText([key.displayNameFr,key.locationLabelFr,key.aliasFr,key.descriptionFr,key.nameEn,key.descriptionEn,key.id,key.rarity==='epic'?'violet violette epique':key.rarity==='legendary'?'doree legendaire or':key.rarityLabelFr].join(' '));
  const keyLocations=[];
  for(const b of allBuildings)for(const f of b.floors){
    for(const door of f.doors){
      const keyId=door.keyId||(door.key?`room_key_${door.key}`:null);if(!keyId||!keyById.has(keyId))continue;
      const room=rooms.find(room=>room.buildingId===b.id&&room.floorLevel===f.level&&`room_key_${room.key}`===keyId);
      keyLocations.push({keyId,b,f,x:door.x,y:door.y,door,room,kind:'door'});
    }
    for(const t of f.targets){
      const keyId=t.keyId?.startsWith('safe_key_')?t.keyId:t.kind==='small'&&t.key?`safe_key_${t.key}`:null;
      if(keyId&&keyById.has(keyId))keyLocations.push({keyId,b,f,x:t.x,y:t.y,t,kind:'safe'});
    }
  }
  const matchesDistrict=b=>districtFilter==='all'||b.district===districtFilter;
  const matchesBuilding=b=>matchesDistrict(b)&&(!searchQuery||matchesText(b.name+' '+b.district)||keyLocations.some(location=>location.b.id===b.id&&matchesKey(keyById.get(location.keyId))));
  const mapBuildings=()=>allBuildings.filter(b=>matchesBuilding(b)&&!hiddenBuildingIds.has(b.id));
  const keyIsShown=key=>layers[keyLayer(key)]&&!hiddenKeyIds.has(key.id);
  const visibleKeyLocations=()=>keyLocations.filter(location=>keyIsShown(keyById.get(location.keyId))&&matchesBuilding(location.b)&&!hiddenBuildingIds.has(location.b.id)&&(!searchQuery||matchesKey(keyById.get(location.keyId))||matchesText(location.b.name)));
  const visibleRooms=()=>visibleKeyLocations().filter(location=>location.room).map(location=>location.room);
  const targetIsShown=t=>layers[t.kind==='computer'?'computers':t.kind]!==false&&!(t.kind==='small'&&t.keyId&&hiddenKeyIds.has(t.keyId));
  function savePreferences(){try{localStorage.setItem('rob-run-atlas-v1',JSON.stringify({layers,hiddenKeys:[...hiddenKeyIds],hiddenBuildings:[...hiddenBuildingIds]}));}catch{}}
  const roomColor=room=>room.rarity==='legendary'?'#a96c0d':'#7843b4';
  const roomTargets=room=>new Set(room?room.targetIds:[]);
  const currentRoom=()=>roomById.get(selectedRoom);
  const plural=(n,word)=>`${n} ${n>1?word.split(' ').map(part=>part+'s').join(' '):word}`;
  function routeOrder(){return routeMode==='split'?routeData.modes.split.circuits.flatMap(c=>c.order):routeData.modes.together.order;}
  function stopLabel(b){
    if(routeMode==='together')return String(routeOrder().indexOf(b.id)+1);
    const circuit=routeData.modes.split.circuits.find(c=>c.order.includes(b.id));
    return circuit.id+(circuit.order.indexOf(b.id)+1);
  }
  function routeSegments(){
    if(routeMode==='split')return routeData.modes.split.circuits.flatMap(c=>c.segments.map(s=>({...s,circuit:c.id})));
    return routeData.modes.together.segments.map(s=>({...s,circuit:owner(byId.get(s.fromId))===owner(byId.get(s.toId))?owner(byId.get(s.fromId)):'link'}));
  }
  function overviewHint(){return routeMode==='split'?'Un secteur chacun : A en violet, B en bleu.':'Suivez les étapes 1 à 12. A fouille le violet, B le bleu.';}
  function rect(){return svg.getBoundingClientRect();}
  function currentFloor(b){return b.floors.find(f=>f.level===(b.id===selected?floorLevel:0))||b.floors[0];}
  function project(x,y){const r=rect();return [(x-view.x)*r.width/view.w,(y-view.y)*r.height/view.h];}
  function unproject(x,y){const r=rect();return [view.x+x*view.w/r.width,view.y+y*view.h/r.height];}
  function point(e){const r=rect();return [e.clientX-r.left,e.clientY-r.top];}
  function visible(x,y,margin=70){const r=rect();const p=project(x,y);return p[0]>-margin&&p[1]>-margin&&p[0]<r.width+margin&&p[1]<r.height+margin;}
  function queueDraw(){if(!drawFrame)drawFrame=requestAnimationFrame(()=>{drawFrame=0;draw();});}
  function setView(next,animate=false){
    cancelAnimationFrame(animation);
    animation=0;animationTarget=null;
    if(!animate||reduceMotion){view=next;queueDraw();return;}
    animationTarget={...next};
    const old={...view},start=performance.now();
    function tick(now){const t=Math.min(1,(now-start)/260),k=1-(1-t)**3;for(const key of ['x','y','w','h'])view[key]=old[key]+(next[key]-old[key])*k;queueDraw();if(t<1)animation=requestAnimationFrame(tick);else{animation=0;animationTarget=null;}}
    animation=requestAnimationFrame(tick);
  }
  function fitted(bounds,padding=1.35){
    const r=rect(),ratio=r.width/r.height;
    const cx=(bounds[0]+bounds[2])/2,cy=(bounds[1]+bounds[3])/2;
    let w=Math.max(bounds[2]-bounds[0],3)*padding,h=Math.max(bounds[3]-bounds[1],3)*padding;
    if(w/h<ratio)w=h*ratio;else h=w/ratio;
    return {x:cx-w/2,y:cy-h/2,w,h};
  }
  function overview(animate=true){
    selected=null;plantSelected=null;floorLevel=0;selectedTarget=null;selectedRoom=null;selectedKeyId=null;updateUI();
    if(viewMode==='trash'){
      const points=filteredTrash(),xs=points.map(p=>p.x),ys=points.map(p=>p.y);
      if(points.length)setView(fitted([Math.min(...xs)-45,Math.min(...ys)-40,Math.max(...xs)+45,Math.max(...ys)+65],1.12),animate);
      else queueDraw();return;
    }
    if(viewMode==='plants'){
      const bs=allBuildings.filter(b=>!plantData.sectors[plantSector].district||b.district===plantData.sectors[plantSector].district);
      const bounds=bs.map(b=>currentFloor(b)?.bounds||[b.x-15,-b.z-15,b.x+15,-b.z+15]);
      setView(fitted([Math.min(...bounds.map(b=>b[0]))-30,Math.min(...bounds.map(b=>b[1]))-30,Math.max(...bounds.map(b=>b[2]))+30,Math.max(...bounds.map(b=>b[3]))+60],1.18),animate);return;
    }
    const bs=mapBuildings(),pts=(bs.length?bs:allBuildings).flatMap(b=>b.floors.length?b.floors.map(f=>[(f.bounds[0]+f.bounds[2])/2,(f.bounds[1]+f.bounds[3])/2]):[[b.x,-b.z]]);
    if(layers.atm)for(const t of data.outdoorTargets||[])pts.push([t.x,t.y]);
    if(layers.trash)for(const t of trashPoints)pts.push([t.x,t.y]);
    const xs=pts.map(p=>p[0]),ys=pts.map(p=>p[1]);
    setView(fitted([Math.min(...xs)-35,Math.min(...ys)-35,Math.max(...xs)+35,Math.max(...ys)+35],1.16),animate);
  }
  function selectBuilding(id,level=0,fit=true){
    const b=byId.get(id);if(!b)return;
    if(viewMode!=='plants')hiddenBuildingIds.delete(id);selected=id;selectedRoom=null;selectedKeyId=null;selectedTarget=null;
    floorLevel=b.floors.some(f=>f.level===level)?level:b.floors[0]?.level||0;
    updateUI();
    const f=currentFloor(b);
    if(fit)setView(fitted(f?f.bounds:[b.x-18,-b.z-18,b.x+18,-b.z+18],1.65),true);else queueDraw();
  }
  function selectKey(id,location){
    const key=keyById.get(id);if(!key)return;
    location=location||keyLocations.find(item=>item.keyId===id);
    layers[keyLayer(key)]=true;hiddenKeyIds.delete(id);selectedKeyId=id;selectedRoom=location?.room?.id||null;selectedTarget=null;
    viewMode='doors';
    if(location){hiddenBuildingIds.delete(location.b.id);selected=location.b.id;floorLevel=location.f.level;}
    else selected=null;
    savePreferences();syncFilters();initRoomList();updateUI();
    if(location){setView(fitted(location.f.bounds,1.65),true);if(location.t)showObject(location.b,location.f,location.t,'target');}
    else queueDraw();
  }
  function selectRoom(id,fit=true){const room=roomById.get(id);if(room)selectKey(`room_key_${room.key}`);}
  function selectRoomFloor(level){
    const b=byId.get(selected);if(!b?.floors.length)return;
    floorLevel=level;selectedTarget=null;updateUI();setView(fitted(currentFloor(b).bounds,1.65),true);
  }
  function setMode(mode){viewMode=mode;if(mode==='routes')layers.route=true;if(mode==='trash')layers.trash=true;const hash=mode==='plants'?'#plantes':mode==='trash'?'#poubelles':'';if(hash)history.replaceState(null,'',hash);else if(['#plantes','#poubelles'].includes(location.hash))history.replaceState(null,'',location.pathname+location.search);syncFilters();initList();initRoomList();overview();savePreferences();}
  function zoom(factor,at){
    cancelAnimationFrame(animation);
    const r=rect(),p=at||[r.width/2,r.height/2],world=unproject(...p);
    const w=Math.max(4,Math.min(2600,view.w/factor)),h=w*r.height/r.width;
    setView({x:world[0]-p[0]/r.width*w,y:world[1]-p[1]/r.height*h,w,h});
  }
  function repel(items,minDistance,bounds=null){
    const a=items.map(item=>({...item,px:item.anchor[0],py:item.anchor[1]}));
    for(let iteration=0;iteration<70;iteration++){
      let moved=0;
      for(let i=0;i<a.length;i++)for(let j=0;j<i;j++){
        let dx=a[i].px-a[j].px,dy=a[i].py-a[j].py,dist=Math.hypot(dx,dy);
        if(dist<minDistance){if(dist<.001){dx=.7;dy=1;dist=Math.hypot(dx,dy);}const push=(minDistance-dist)*.51;dx=dx/dist*push;dy=dy/dist*push;a[i].px+=dx;a[i].py+=dy;a[j].px-=dx;a[j].py-=dy;moved+=push;}
      }
      if(bounds)for(const item of a){const x=Math.max(bounds.left,Math.min(bounds.right,item.px)),y=Math.max(bounds.top,Math.min(bounds.bottom,item.py));moved+=Math.abs(x-item.px)+Math.abs(y-item.py);item.px=x;item.py=y;}
      if(moved<.02)break;
    }
    return a;
  }
  function accessible(g,label){g.setAttribute('tabindex','0');g.setAttribute('role','button');g.setAttribute('aria-label',label);}
  function wireAction(g,action){
    g.addEventListener('click',e=>{if(clickSuppressed)return;e.stopPropagation();action();});
    g.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();e.stopPropagation();action();}});
  }
  function routePath(points,u,dashed=false,color=routeColors.A){
    if(!points||points.length<2)return;
    const d=points.map((p,i)=>(i?'L':'M')+p[0]+' '+p[1]).join('');
    const common={d,fill:'none','stroke-linecap':'round','stroke-linejoin':'round'};
    if(dashed)common['stroke-dasharray']=`${3*u} ${5*u}`;
    groups.route.append(el('path',{...common,stroke:'#fffdf7','stroke-width':(dashed?6:8)*u,'stroke-opacity':.95}));
    groups.route.append(el('path',{...common,stroke:color,'stroke-width':(dashed?2.5:4.5)*u,'data-route-kind':dashed?'approach':'street'}));
  }
  function routeArrows(points,u){
    const legs=[];let total=0;
    for(let i=1;i<points.length;i++){
      const a=points[i-1],b=points[i],length=Math.hypot(b[0]-a[0],b[1]-a[1]);
      if(length>0){legs.push({a,b,start:total,length});total+=length;}
    }
    const pixels=total/u;if(pixels<30)return;
    const distances=pixels<150?[total/2]:Array.from({length:Math.max(1,Math.floor((pixels-35)/115))},(_,i)=>(55+i*115)*u);
    for(const distance of distances){
      const leg=legs.find(l=>distance>=l.start&&distance<=l.start+l.length);if(!leg)continue;
      const t=(distance-leg.start)/leg.length,x=leg.a[0]+t*(leg.b[0]-leg.a[0]),y=leg.a[1]+t*(leg.b[1]-leg.a[1]);
      if(!visible(x,y,20))continue;
      const angle=Math.atan2(leg.b[1]-leg.a[1],leg.b[0]-leg.a[0])*180/Math.PI;
      const g=el('g',{transform:`translate(${x} ${y}) rotate(${angle}) scale(${u})`,'data-route-arrow':'true'});
      g.append(el('path',{d:'M-5 -6L4 0L-5 6',fill:'none',stroke:'#fff','stroke-width':3.4,'stroke-linecap':'round','stroke-linejoin':'round'}));
      groups.route.append(g);
    }
  }
  function drawRoute(u,scale){
    if(scale>=5)return;
    const segments=routeSegments();
    for(const segment of segments){
      const color=routeColors[segment.circuit]||routeColors.A;
      routePath(segment.roadPoints||segment.points,u,false,color);
      routePath(segment.fromAccess,u,true,color);routePath(segment.toAccess,u,true,color);
    }
    for(const segment of segments)routeArrows(segment.roadPoints||segment.points,u);
  }
  function keyColor(key){return key.rarity==='epic'?'#7843b4':key.rarity==='legendary'?'#a96c0d':key.rarity==='exotic'?'#b33c51':'#238158';}
  function keyMark(key){return key.family==='room_key'?String(key.key):key.family==='safe_key'?'C'+key.key:'▣';}
  function shortName(b){return b.name.replace('Magasin d’équipement','Équipement').replace(' Sunny Beach','').replace(' Downtown','').replace(' — clé 7','').replace('Station-service Oil-Up','Station Oil-Up');}
  function drawAccess(location,u,position,city=false){
    const key=keyById.get(location.keyId),color=keyColor(key),xy=unproject(...position),active=selectedKeyId===key.id;
    groups.doors.append(el('line',{x1:location.x,y1:location.y,x2:xy[0],y2:xy[1],stroke:color,'stroke-width':u*1.4}));
    groups.doors.append(el('path',{d:`M${location.x-3*u} ${location.y-3*u}l${6*u} ${6*u}m0 ${-6*u}l${-6*u} ${6*u}`,stroke:color,'stroke-width':u*2.4,'stroke-linecap':'round'}));
    const g=el('g',{transform:`translate(${xy[0]} ${xy[1]}) scale(${u})`,class:'key-door-group','data-key':key.id});
    if(city){
      g.append(el('circle',{r:23,fill:'transparent'}));
      g.append(el('circle',{r:18,fill:color,stroke:active?'#15262b':'#fff','stroke-width':active?3:2,class:'room-key-badge'}));
      g.append(el('text',{'text-anchor':'middle','dominant-baseline':'central','font-size':key.family==='room_key'?16:13,'font-weight':850,fill:'#fff'},keyMark(key)));
      const text=layers.labels?shortName(location.b):location.room?plural(location.room.drillCount,'coffre'):key.displayNameFr;
      const width=Math.min(150,Math.max(54,text.length*5.6+12));
      g.append(el('rect',{x:-width/2,y:21,width,height:19,rx:5,fill:'#fffdf7'}));
      g.append(el('text',{x:0,y:31,'text-anchor':'middle','dominant-baseline':'central','font-size':10,'font-weight':800,fill:color},text));
    }else{
      const title=key.family==='room_key'?'Clé de pièce':key.displayNameFr,sub=shortName(location.b),width=Math.min(190,Math.max(132,sub.length*5.8+18));
      g.append(el('rect',{x:-width/2,y:-23,width,height:46,rx:7,fill:color,stroke:'#fff','stroke-width':active?2.5:1.5}));
      g.append(el('text',{x:0,y:-8,'text-anchor':'middle','dominant-baseline':'central','font-size':12,'font-weight':850,fill:'#fff'},title));
      g.append(el('text',{x:0,y:9,'text-anchor':'middle','dominant-baseline':'central','font-size':10,'font-weight':650,fill:'#fff'},sub));
    }
    const label=`${key.displayNameFr} — ${keyPlace(key.id)}. ${key.descriptionFr} ${location.f.label}.`;
    accessible(g,label);g.append(el('title',{},label));wireAction(g,()=>selectKey(key.id,location));groups.doors.append(g);
  }
  function renderBuildingMarker(m,u){
    const xy=unproject(m.px,m.py),inRoute=buildings.some(b=>b.id===m.b.id),showRoute=layers.route&&inRoute,color=showRoute?routeColors[owner(m.b)]:'#395b66';
    if(Math.hypot(m.px-m.anchor[0],m.py-m.anchor[1])>4)groups.buildings.append(el('line',{x1:m.x,y1:m.y,x2:xy[0],y2:xy[1],stroke:color,'stroke-width':u*1.1}));
    const g=el('g',{transform:`translate(${xy[0]} ${xy[1]}) scale(${u})`,class:'building-marker','data-building':m.b.id});
    g.append(el('rect',{x:-17,y:-17,width:34,height:34,rx:9,fill:color,stroke:'#fff','stroke-width':1.7}));
    g.append(el('text',{'text-anchor':'middle','dominant-baseline':'central','font-size':showRoute?12:14,'font-weight':850,fill:'#fff'},showRoute?stopLabel(m.b):m.b.floors.length?String(m.count):'?'));
    if(layers.labels){const name=shortName(m.b),width=Math.min(155,Math.max(50,name.length*5.2+10));g.append(el('rect',{x:-width/2,y:20,width,height:18,rx:4,fill:'#fffdf7'}));g.append(el('text',{x:0,y:29,'text-anchor':'middle','dominant-baseline':'central','font-size':9,'font-weight':750,fill:color},name));}
    const label=`${m.b.name}, ${m.b.district}, ${m.count} repères activés. ${m.b.floors.length?'Voir les plans intérieurs.':'Plan intérieur indisponible.'}`;
    accessible(g,label);g.append(el('title',{},label));wireAction(g,()=>selectBuilding(m.b.id));groups.buildings.append(g);
  }
  function filteredTrash(){
    if(/^\d+$/.test(trashQuery.trim()))return trashPoints.filter(p=>p.n===Number(trashQuery.trim()));
    const words=normalize(trashQuery).trim().split(/\s+/).filter(Boolean);
    return trashPoints.filter(p=>words.every(word=>normalize(`${p.n} poubelle benne ${p.district} ${p.nearby}`).includes(word)));
  }
  function updateTrashUI(){
    const points=filteredTrash();
    $('sidebar-eyebrow').textContent='LOOTY BAY · POINTS DE FOUILLE';
    $('sidebar-title').textContent=`${trashPoints.length} poubelles répertoriées`;
    document.querySelector('.intro').textContent='Toutes les poubelles fouillables des deux cartes sources, à leurs coordonnées. Clique pour te situer.';
    $('room-detail').hidden=true;$('floor-bar').hidden=true;
    $('location-district').textContent='TOUTE LA VILLE · 4 QUARTIERS';
    $('location-title').textContent=trashQuery?'Poubelles · '+points.length+' résultat'+(points.length>1?'s':''):'Les poubelles de Looty Bay';
    $('location-subtitle').textContent='Zoome pour séparer les repères proches. Le petit point au bout du trait indique l’emplacement exact.';
    $('trash-coverage').textContent=Object.entries(trashData.districtCounts).map(([name,count])=>`${name} : ${count}`).join(' · ');
    $('trash-result-count').textContent=`${points.length} / ${trashPoints.length} emplacements affichés`;
    $('trash-source-note').textContent=`${trashPoints.length} nœuds de butin recoupés entre RobRun.fun et ROB RUN Info, le 18/11/2026. Les deux types de bennes fouillables sont inclus ; les décors et les objets éparpillés au sol sont exclus. Données du build ${trashData.build.robrunInfoBuild} (${trashData.build.robrunInfoDataDate}), sans vérification dans une partie en cours.`;
    const list=$('trash-list');list.replaceChildren();
    for(const p of points){
      const button=document.createElement('button');button.type='button';button.className='trash-list-button';button.dataset.trashId=p.id;
      button.innerHTML=`<span class="trash-number">${p.n}</span><span><strong>Poubelle ${p.n} · ${escape(p.district)}</strong><small>Près de ${escape(p.nearby)}</small></span><span aria-hidden="true">↗</span>`;
      button.addEventListener('click',()=>showTrash(p,true));list.append(button);
    }
    if(!points.length)list.innerHTML='<p class="empty-results">Aucune poubelle ne correspond. Efface la recherche pour revoir toute la ville.</p>';
    $('building-summary').innerHTML=`<div><strong>${points.length} emplacements visibles sur ${trashPoints.length} répertoriés.</strong><br><span>Deux sources concordantes · contenu et disponibilité à vérifier dans ta partie.</span></div>`;
  }
  function showTrash(p,fit=false){
    selected=null;plantSelected=null;selectedRoom=null;selectedKeyId=null;updateUI();selectedTarget=p.id;
    const box=$('object-detail');box.hidden=false;box.style.borderLeftColor='#efbc57';
    box.innerHTML=`<div class="object-heading"><div><h3>Poubelle fouillable ${p.n}</h3><p class="object-place">${escape(p.district)} · près de ${escape(p.nearby)}</p></div><span class="trash-number">${p.n}</span></div><p class="object-action">Inspecte la poubelle au point indiqué. Ce repère est un nœud de butin répertorié, pas un élément décoratif.</p><p class="object-place">Coordonnées du plan : X ${p.x.toFixed(1)} · Z ${p.z.toFixed(1)}.<br>Le bâtiment voisin sert uniquement de repère pour t’orienter.</p><p class="object-access">Le butin restant et le délai de réapparition ne sont pas connus.</p><p class="room-source"><a href="https://robrun.fun/en/" target="_blank" rel="noopener noreferrer">RobRun.fun</a> · <a href="https://robrun.info/map/" target="_blank" rel="noopener noreferrer">ROB RUN Info</a> · deux positions concordantes</p><button type="button" class="object-close">Fermer le détail</button>`;
    wireObjectClose();
    if(fit){setView(fitted([p.x-65,p.y-65,p.x+65,p.y+80],1.2),true);if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});}
    queueDraw();
  }
  function drawTrash(u,scale){
    $('trash-map-legend').hidden=!layers.trash;
    if(!layers.trash)return;
    const points=(viewMode==='trash'?filteredTrash():trashPoints).filter(p=>visible(p.x,p.y,20));
    const r=rect(),margin=coarse?24:18;
    const markers=repel(points.map(p=>({p,anchor:project(p.x,p.y)})),coarse?42:29,{left:margin,right:r.width-margin,top:margin,bottom:r.height-34});
    for(const marker of markers){
      const p=marker.p,[x,y]=unproject(marker.px,marker.py),active=selectedTarget===p.id;
      if(Math.hypot(marker.px-marker.anchor[0],marker.py-marker.anchor[1])>2){
        groups.trash.append(el('line',{x1:p.x,y1:p.y,x2:x,y2:y,stroke:'#654c25','stroke-width':u*1.2}));
        groups.trash.append(el('circle',{cx:p.x,cy:p.y,r:u*2.5,fill:'#523b1a',stroke:'#fff','stroke-width':u*.7}));
      }
      const g=el('g',{transform:`translate(${x} ${y}) scale(${u})`,class:'trash-marker','data-trash-id':p.id,'data-trash-x':p.x,'data-trash-y':p.y});
      g.append(el('circle',{r:coarse?21:16,fill:'transparent'}));
      g.append(el('rect',{x:-12,y:-12,width:24,height:24,rx:5,fill:active?'#5d4016':'#8b621e',stroke:active?'#fff1ad':'#fff9e8','stroke-width':active?3:1.8}));
      g.append(el('path',{d:'M-5 -4h10l-1 10h-8zM-7 -6h14M-2 -8h4M-2 -1v5M2 -1v5',fill:'none',stroke:'#fff2c8','stroke-width':1.3,'stroke-linecap':'round','stroke-linejoin':'round'}));
      if(scale>1.6||active){g.append(el('rect',{x:-11,y:13,width:22,height:15,rx:4,fill:'#fff8df'}));g.append(el('text',{x:0,y:21,'text-anchor':'middle','dominant-baseline':'central','font-size':10,'font-weight':800,fill:'#5e4219'},String(p.n)));}
      const label=`Poubelle fouillable ${p.n}, ${p.district}, près de ${p.nearby}`;
      accessible(g,label);g.append(el('title',{},label));wireAction(g,()=>showTrash(p));groups.trash.append(g);
    }
  }
  function locatePlant(id){
    const point=plantData.stops[id];if(!point)return;plantSelected=id;
    selectBuilding(point.buildingId,point.floorLevel);
    if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});
  }
  function updatePlantUI(){
    const order=plantOrder(),route=plantRouteOrder(),next=nextPlant(),done=route.filter(id=>plantDone.has(id)).length,b=byId.get(selected),point=plantData.stops[plantSelected];
    const count=kind=>order.filter(id=>plantData.stops[id].kind===kind).length;
    $('sidebar-eyebrow').textContent='LANCEMENT RAPIDE · REPÉRAGE EN CIVIL';
    $('sidebar-title').textContent='Plantes · toute la ville';
    document.querySelector('.intro').textContent='Strip-club, hôtels, magasins, café, station et manoir : suis le tracé et coche les espaces ouverts vérifiés.';
    $('room-detail').hidden=true;$('floor-bar').hidden=true;
    $('location-district').textContent=plantData.sectors[plantSector].label.toUpperCase()+' · '+(plantExtra?'REPÉRAGE ÉTENDU':'TRACÉ SANS CLÉ');
    $('location-title').textContent=point?`${point.label} · ${plantName(point)}`:`Plantes · ${route.length} contrôles dans la tournée`;
    $('location-subtitle').textContent=point?point.where:'Le tracé inclut aussi l’étage du strip-club et les deux côtés des halls des hôtels jaune et bleu. Les plants restent à vérifier sur place.';
    $('plant-sector').value=plantSector;$('plant-extra').checked=plantExtra;
    $('plant-coverage').textContent=order.length?`${count('exact')} positions précises + ${count('reported')} contrôles au club et aux hôtels + ${count('named')} zones citées. ${count('prospect')} autres lieux de prospection disponibles.`:'Aucune position de plant documentée à Palmside dans les sources consultées. Cela ne prouve pas qu’aucun plant ne peut y apparaître.';
    $('plant-progress').textContent=`${done} / ${route.length} étapes du tracé vérifiées`;
    $('plant-storage-note').textContent=plantStorage?'Les coches sont conservées dans ce navigateur.':'Stockage du navigateur indisponible : les coches restent valables jusqu’à la fermeture de cette page.';
    const nextStop=plantData.stops[next];
    $('plant-next').innerHTML=next?`<span class="eyebrow">PROCHAINE ÉTAPE · ${escape(nextStop.label)}</span><strong>${escape(plantName(nextStop))}</strong><p>${escape(nextStop.where)}</p>${nextStop.kind==='reported'?'<p>Zone signalée en civil · plant à vérifier sur place.</p>':nextStop.kind!=='exact'?'<p>Inspecte seulement les espaces déjà ouverts.</p>':''}<button type="button" id="plant-go">Voir où regarder ↗</button>`:route.length?'<strong>Tracé vérifié.</strong><p>Tu peux étendre la prospection, changer de quartier ou commencer une nouvelle tournée.</p>':'<strong>Aucun point sans clé documenté ici.</strong><p>Les éventuels repères ? restent consultables. Leur accès et la présence d’un plant sont à vérifier.</p>';
    $('plant-go')?.addEventListener('click',()=>locatePlant(next));
    const lists={exact:$('plant-checklist'),reported:$('plant-reported'),named:$('plant-zones'),prospect:$('plant-prospects-list')};Object.values(lists).forEach(list=>list.replaceChildren());
    order.forEach(id=>{
      const p=plantData.stops[id],building=byId.get(p.buildingId),checked=plantDone.has(id),row=document.createElement('li');
      row.className='plant-stop plant-kind-'+p.kind+(checked?' is-done':'')+(id===next?' is-next':'');row.dataset.stop=id;
      const status=p.kind==='exact'?'Position signalée · RDC':p.kind==='reported'?`Signalé en civil · ${p.floorLevel===1?'1er étage':'RDC'}`:p.kind==='named'?'Zone citée · parties ouvertes seulement':'Prospection · aucun spawn confirmé';
      row.innerHTML=`<label class="plant-check"><input type="checkbox" data-plant-done="${id}" ${checked?'checked':''} aria-label="Point ${escape(p.label)} vérifié : ${escape(plantName(p))}"><span class="plant-number">${escape(p.label)}</span><span><strong>${escape(plantName(p))}</strong><small>${checked?'Vérifié · ':id===next?'Prochain · ':''}${status}</small></span></label><button type="button" class="plant-locate" aria-label="Voir le repère ${escape(p.label)} sur la carte">↗</button><p>${escape(p.where)}</p><details class="plant-evidence"><summary>Source et accès</summary><p>${escape(p.evidence)}</p><p>${escape(p.access)}</p><a href="${escape(p.sources[0])}" target="_blank" rel="noopener noreferrer">Consulter la source ↗</a></details>`;
      row.querySelector('input').addEventListener('change',event=>{
        if(event.target.checked)plantDone.add(id);else plantDone.delete(id);
        savePlants();updateUI();queueDraw();
        $('plant-panel').querySelector(`[data-plant-done="${id}"]`)?.focus({preventScroll:true});
      });
      row.querySelector('button').addEventListener('click',()=>locatePlant(id));lists[p.kind].append(row);
    });
    for(const [kind,list] of Object.entries(lists))if(!list.children.length)list.innerHTML=`<li class="plant-empty">${kind==='exact'?'Aucune position précise documentée dans ce quartier.':'Aucun repère de cette catégorie dans ce quartier.'}</li>`;
    $('plant-prospects-title').textContent=`? · ${count('prospect')} autres lieux à prospecter`;
    $('building-summary').innerHTML=`<div><strong>${point?escape(point.evidence):'Tournée de repérage : strip-club, hôtels et autres lieux signalés. Présence des plants variable.'}</strong><br><span>${plantExtra?'Prospection étendue. ':'Positions et zones citées incluses dans le tracé. '}Reste dans les espaces ouverts. Traits pleins : rues · pointillés : approche indicative.</span></div><span class="plant-summary-count">${done}/${route.length} vérifiés</span>`;
  }
  function drawPlants(u,scale){
    const order=plantOrder(),next=nextPlant(),segments=window.PLANT_ROUTE_DATA?.segments||{},route=[...new Set(plantRouteOrder().map(id=>plantData.stops[id].buildingId))];
    let missing=0;
    for(let i=1;i<route.length;i++){
      const fromId=route[i-1],toId=route[i],segment=segments[fromId+'|'+toId],color=plantExtra?'#99722c':'#147955';
      if(segment){routePath(segment.roadPoints,u,false,color);if(segment.fromAccess?.length)routePath(segment.fromAccess,u,true,color);if(segment.toAccess?.length)routePath(segment.toAccess,u,true,color);routeArrows(segment.roadPoints,u);}else missing++;
    }
    const markers=[],painted=new Set();
    order.forEach(id=>{
      const p=plantData.stops[id],b=byId.get(p.buildingId),f=b.floors.find(f=>f.level===p.floorLevel)||b.floors[0],{x,y}=p,done=plantDone.has(id),color=done?'#718278':p.kind==='exact'?'#147955':p.kind==='reported'?'#087e91':p.kind==='named'?'#a46513':'#6b6871';
      if(f&&!painted.has(b.id)){
        painted.add(b.id);const shape=el('g',{'data-plant-building':b.id,'data-plant-floor':f.level});
        shape.append(el('path',{d:f.outline,fill:p.kind==='exact'?'#d1ebd3':'#e9e0c9',stroke:color,'stroke-width':1.2*u}));
        if(scale>2)shape.append(el('path',{d:f.walls,fill:'#5b7264',stroke:'#5b7264','stroke-width':u*.3}));
        wireAction(shape,()=>locatePlant(id));groups.shapes.append(shape);
      }
      if(visible(x,y))markers.push({id,p,b,x,y,done,color,anchor:project(x,y)});
    });
    const r=rect(),compact=r.width<600||scale<1.2,margin=compact?24:68;
    for(const m of repel(markers,compact?45:90,{left:margin,right:r.width-margin,top:48,bottom:r.height-95})){
      const xy=unproject(m.px,m.py),g=el('g',{transform:`translate(${xy[0]} ${xy[1]}) scale(${u})`,class:'plant-marker','data-plant-stop':m.id,'data-plant-kind':m.p.kind,'data-next':String(m.id===next)});
      if(Math.hypot(m.px-m.anchor[0],m.py-m.anchor[1])>4)groups.buildings.append(el('line',{x1:m.x,y1:m.y,x2:xy[0],y2:xy[1],stroke:m.color,'stroke-width':u}));
      groups.buildings.append(el('circle',{cx:m.x,cy:m.y,r:3*u,fill:m.color,stroke:'#fff','stroke-width':u,'data-plant-anchor':m.id}));
      g.append(el('circle',{r:compact?18:22,fill:'#fffdf5',stroke:m.color,'stroke-width':m.id===next||m.id===plantSelected?4:2}));
      g.append(el('circle',{r:compact?14:17,fill:m.color}));
      g.append(el('text',{'text-anchor':'middle','dominant-baseline':'central','font-size':m.p.label.length>1?11:15,'font-weight':850,fill:'#fff'},m.done?'✓':m.p.label));
      if(!compact){const name=shortName(m.b),width=Math.min(130,Math.max(70,name.length*5.3+12));g.append(el('rect',{x:-width/2,y:25,width,height:20,rx:5,fill:'#fffdf5'}));g.append(el('text',{x:0,y:35,'text-anchor':'middle','dominant-baseline':'central','font-size':10,'font-weight':750,fill:m.color},name));}
      const label=`${m.p.label} : ${plantName(m.p)}. ${m.done?'Point vérifié.':m.p.kind==='exact'?'Position de plant signalée.':m.p.kind==='reported'?'Zone signalée en civil, repère du bâtiment ou de l’étage.':m.p.kind==='named'?'Zone citée, accès à vérifier.':'Prospection, aucun spawn confirmé.'}`;
      accessible(g,label);g.append(el('title',{},label));wireAction(g,()=>locatePlant(m.id));groups.buildings.append(g);
    }
    const p=plantData.stops[next];
    $('map-hint').textContent=(p?`Prochain ${p.label} · ${p.title||shortName(byId.get(p.buildingId))}`:order.length?'Aucune étape restante dans le tracé sélectionné':'Aucun emplacement de plant documenté ici')+(missing?` · ${missing} liaison(s) sans trajet vérifié`:'');
  }
  function draw(){
    const r=rect();if(r.width<1||r.height<1)return;
    svg.setAttribute('viewBox',`${view.x} ${view.y} ${view.w} ${view.h}`);
    Object.values(groups).forEach(g=>g.replaceChildren());
    const u=view.w/r.width,scale=1/u,detailMode=scale>=5||!!byId.get(selected)?.floors.length,room=currentRoom(),inside=roomTargets(room),activeBuildings=mapBuildings();
    drawTrash(u,scale);
    if(viewMode==='trash'){$('map-hint').textContent='Poubelles fouillables · clique sur un repère pour le situer';return;}
    if(viewMode==='plants'){drawPlants(u,scale);return;}
    if(layers.route)drawRoute(u,scale);
    const objects=[],markers=[],access=[];
    const allowedLocations=visibleKeyLocations().filter(location=>location.kind==='door');
    for(const b of activeBuildings){
      const f=currentFloor(b),active=b.id===selected;
      if(f){
        const shape=el('g',{'data-building':b.id});
        shape.append(el('path',{d:f.outline,fill:active?'#f3f1e8':'#e5eadb',stroke:active?'#70528d':'#738479','stroke-width':u*(active?1.8:1),'fill-opacity':active?1:.87}));
        if(scale>2||active)shape.append(el('path',{d:f.walls,fill:active?'#4c6059':'#64766d',stroke:active?'#4c6059':'#64766d','stroke-width':u*.4}));
        wireAction(shape,()=>selectBuilding(b.id));groups.shapes.append(shape);
        if(detailMode){
          for(const t of f.targets)if(targetIsShown(t)&&visible(t.x,t.y))objects.push({b,f,t,type:t.kind==='computer'?'computer':'target',anchor:project(t.x,t.y)});
          const targetIds=new Set(f.targets.map(t=>t.id));
          for(const point of f.sourcePoints||[]){
            if(targetIds.has(point.id)||!visible(point.x,point.y))continue;
            const security=point.sourceType==='alarm'||point.sourceType==='camera';
            if(security&&layers.security||['loot','obj'].includes(point.sourceType)&&layers.loot)objects.push({b,f,t:point,type:security?'security':'loot',anchor:project(point.x,point.y)});
          }
          if(layers.otherKeys||layers.drill)for(const point of f.accessPoints||[])if(visible(point.x,point.y))objects.push({b,f,t:point,type:'access',anchor:project(point.x,point.y)});
          if(layers.otherKeys)for(const door of f.doors){
            if(door.keyId||!visible(door.x,door.y))continue;
            const color=door.pickable?'#32728d':'#6c7777';
            groups.doors.append(el('path',{d:`M${door.x-2.6*u} ${door.y-2.6*u}l${5.2*u} ${5.2*u}m0 ${-5.2*u}l${-5.2*u} ${5.2*u}`,stroke:color,'stroke-width':u*1.3,opacity:.6}));
          }
        }
      }
      if(!detailMode){
        const x=f?(f.bounds[0]+f.bounds[2])/2:b.x,y=f?(f.bounds[1]+f.bounds[3])/2:-b.z;
        const hasDoor=allowedLocations.some(location=>location.b.id===b.id),count=b.floors.flatMap(f=>f.targets).filter(targetIsShown).length;
        const routeStop=layers.route&&buildings.some(stop=>stop.id===b.id);
        if(visible(x,y)&&(!hasDoor||routeStop)&&(count||routeStop||!b.floors.length&&layers.labels||layers.loot||layers.security))markers.push({b,x,y,count,anchor:project(x,y)});
      }
    }
    for(const location of allowedLocations)if(visible(location.x,location.y)&&(!detailMode||currentFloor(location.b)?.level===location.f.level))access.push({location,anchor:project(location.x,location.y)});
    if(layers.atm)for(const t of data.outdoorTargets||[])if(visible(t.x,t.y)&&(!searchQuery||matchesText(t.label)))objects.push({b:null,f:null,t,type:'target',anchor:project(t.x,t.y)});
    if(!detailMode){
      for(const m of repel([...markers.map(m=>({...m,markerType:'building'})),...access.map(m=>({...m,markerType:'access'}))],layers.labels?83:57)){
        if(m.markerType==='building')renderBuildingMarker(m,u);else drawAccess(m.location,u,[m.px,m.py],true);
      }
    }
    const placed=repel(objects,coarse?43:34);
    for(const m of placed){
      const {b,f,t}=m,xy=unproject(m.px,m.py),inRoom=room?inside.has(t.id)||room.computers.some(pc=>pc.id===t.id):viewMode==='routes'&&b&&buildings.some(stop=>stop.id===b.id)?inPlan(b,t):true;
      const selectedObject=selectedTarget===t.id,isExtra=['loot','security','access'].includes(m.type),base=m.type==='security'?'#b5493e':m.type==='loot'?'#686249':colors[t.kind]||'#17668d',color=inRoom?base:'#899398';
      if(Math.hypot(m.px-m.anchor[0],m.py-m.anchor[1])>3){groups.leaders.append(el('line',{x1:t.x,y1:t.y,x2:xy[0],y2:xy[1],stroke:color,'stroke-width':u}));groups.leaders.append(el('circle',{cx:t.x,cy:t.y,r:u*2.8,fill:color,stroke:'#fff','stroke-width':u*.6}));}
      const g=el('g',{transform:`translate(${xy[0]} ${xy[1]}) scale(${u})`,class:'target-marker'+(!inRoom?' outside-room':''),'data-target':t.id,'data-in-room':String(inRoom),'data-kind':m.type==='target'?t.kind:m.type});
      g.append(el('circle',{r:coarse?22:17,fill:'transparent'}));
      if(selectedObject)g.append(el('circle',{r:21,fill:'none',stroke:'#15282b','stroke-width':2,'stroke-dasharray':'3 3'}));
      const attrs={fill:color,stroke:'#fff','stroke-width':1.6,'fill-opacity':inRoom?1:.7};
      if(t.kind==='drill'||t.kind==='computer'||t.kind==='atm')g.append(el('rect',{x:-15,y:-14,width:30,height:28,rx:4,...attrs}));
      else if(t.kind==='small'||t.kind==='deposit')g.append(el('path',{d:'M0 -18 L18 0 L0 18 L-18 0 Z',...attrs}));
      else if(isExtra)g.append(el('circle',{r:10,...attrs}));
      else g.append(el('circle',{r:14.5,...attrs}));
      const text=m.type==='computer'?'PC':m.type==='loot'?'•':m.type==='security'?'!':m.type==='access'?'D':gainBadge(t);
      g.append(el('text',{'text-anchor':'middle','dominant-baseline':'central','font-size':m.type==='computer'?10:12,'font-weight':800,fill:'#fff'},text));
      const label=`${t.label||t.sourceLabel}, ${b?b.name:'ville'}, ${f?f.label:'distributeur'}. ${m.type==='computer'?'Outil USB':isExtra?'Repère sans gain caméra attribué':gainBadge(t)+' caméra par action créditée'}.${room?(inRoom?' Dans la salle.':' Hors de la salle sélectionnée.'):''}`;
      accessible(g,label);g.append(el('title',{},label));wireAction(g,()=>showObject(b,f,t,m.type));groups.targets.append(g);
    }
    if(detailMode){
      const obstacles=placed.slice();
      for(const marker of access){
        const options=[[100,-40],[100,40],[-100,-40],[-100,40],[0,-85],[0,85],[135,0],[-135,0]];let best=options[0],score=Infinity;
        for(const offset of options){const x=marker.anchor[0]+offset[0],y=marker.anchor[1]+offset[1];let penalty=x<100||x>r.width-100||y<65||y>r.height-90?1e6:0;for(const obstacle of obstacles){const dx=Math.abs(obstacle.px-x),dy=Math.abs(obstacle.py-y);if(dx<110&&dy<44)penalty+=(110-dx)*(44-dy);}if(penalty<score){score=penalty;best=offset;}}
        const position=[marker.anchor[0]+best[0],marker.anchor[1]+best[1]];drawAccess(marker.location,u,position);obstacles.push({px:position[0],py:position[1]});
      }
    }
    $('map-hint').textContent=detailMode?(room?'Croix = porte exacte · Gris = hors de la salle sélectionnée':'Chaque repère est cliquable · Gains caméra par action créditée'):'Toute la ville · Cliquez sur un bâtiment ou recherchez votre clé.';
    document.querySelector('.route-legend').hidden=!layers.route||detailMode;
    document.querySelector('.optional-legend').textContent=room?'Grisé = hors de cette salle':'Repères = objets, portes et accès';
    document.querySelector('.room-computer-legend').hidden=!layers.computers;
    for(const name of ['furniture','drill','small','deposit']){const legend=document.querySelector('.'+name+'-legend');if(legend)legend.hidden=!layers[name];}
    $('gain-note').textContent='+ = points / action créditée';
  }

  function syncFilters(){
    document.querySelectorAll('[data-layer]').forEach(input=>{input.checked=!!layers[input.dataset.layer];});
  }
  function initRoomList(){
    const list=$('room-list');list.replaceChildren();
    const matches=keyCatalog.filter(key=>matchesKey(key)&&(districtFilter==='all'||keyLocations.some(location=>location.keyId===key.id&&matchesDistrict(location.b))));
    $('key-result-count').textContent=String(matches.length);
    for(const key of matches){
      const location=keyLocations.find(item=>item.keyId===key.id),room=location?.room,shown=keyIsShown(key);
      const row=document.createElement('div');row.className='key-list-row'+(key.rarity==='legendary'?' is-legendary':'');
      const checkbox=document.createElement('input');checkbox.type='checkbox';checkbox.className='toggle-key';checkbox.checked=shown;
      checkbox.setAttribute('aria-label',`Afficher ${key.displayNameFr} — ${keyPlace(key.id)}`);
      checkbox.addEventListener('change',()=>{
        if(checkbox.checked){layers[keyLayer(key)]=true;hiddenKeyIds.delete(key.id);}else hiddenKeyIds.add(key.id);
        savePreferences();syncFilters();updateUI();queueDraw();
      });row.append(checkbox);
      const button=document.createElement('button');button.type='button';button.className='room-row'+(key.rarity==='legendary'?' is-legendary':'');button.dataset.key=key.id;button.setAttribute('aria-pressed',String(selectedKeyId===key.id));
      button.setAttribute('aria-label',`${key.displayNameFr} — ${keyPlace(key.id)}. ${key.descriptionFr} Voir l’emplacement.`);
      button.innerHTML=`<img class="key-icon" src="${escape(key.icon)}" alt=""><span class="room-label"><strong class="key-name">${escape(key.displayNameFr)}</strong><small>${escape(keyPlace(key.id))}</small><span class="key-description">${escape(key.descriptionFr)}</span><span class="key-meta">${escape(key.rarityLabelFr)}${location?' · '+escape(location.f.label):' · emplacement à confirmer'}${key.family==='room_key'?' · repère '+key.key:''}</span></span>${room?`<span class="room-count">${room.drillCount}<small>coffre${room.drillCount>1?'s':''}</small></span>`:'<span></span>'}`;
      button.addEventListener('click',()=>{selectKey(key.id);if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});});row.append(button);list.append(row);
    }
    if(!matches.length)list.innerHTML='<p class="empty-results">Aucune clé trouvée. Essaie le nom du bâtiment ou un mot de la description.</p>';
    initBuildingIndex();
  }
  function initBuildingIndex(){
    const list=$('atlas-building-list');list.replaceChildren();const bs=allBuildings.filter(matchesBuilding);
    $('atlas-building-count').textContent=String(bs.length);
    for(const b of bs){
      const row=document.createElement('div');row.className='key-list-row building-list-row';
      const checkbox=document.createElement('input');checkbox.type='checkbox';checkbox.className='toggle-key';checkbox.checked=!hiddenBuildingIds.has(b.id);checkbox.setAttribute('aria-label',`Afficher le bâtiment ${b.name}`);
      checkbox.addEventListener('change',()=>{if(checkbox.checked)hiddenBuildingIds.delete(b.id);else hiddenBuildingIds.add(b.id);if(hiddenBuildingIds.has(selected)){selected=null;selectedRoom=null;selectedKeyId=null;}savePreferences();updateUI();queueDraw();});row.append(checkbox);
      const button=document.createElement('button');button.type='button';button.className='atlas-building-row';button.dataset.building=b.id;button.setAttribute('aria-pressed',String(selected===b.id));
      const count=b.floors.flatMap(f=>f.targets).length;
      button.innerHTML=`<span><strong>${escape(b.name)}</strong><small>${escape(b.district)} · ${b.floors.length?b.floors.length+' plan'+(b.floors.length>1?'s d’étages':' d’étage'):'intérieur non documenté'}</small></span><span class="building-count">${count?count+' cibles':'Plan ?'}</span>`;
      button.addEventListener('click',()=>{viewMode='doors';selectBuilding(b.id);if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});});row.append(button);list.append(row);
    }
    if(!bs.length)list.innerHTML='<p class="empty-results">Aucun bâtiment correspondant.</p>';
  }
  function updateAtlasStats(){
    $('atlas-coverage').textContent=`${allBuildings.length} bâtiments · ${allBuildings.filter(b=>b.floors.length).length} intérieurs · ${allBuildings.reduce((sum,b)=>sum+b.floors.length,0)} plans d’étages`;
    const locations=visibleKeyLocations().filter(location=>location.kind==='door');
    $('room-total').textContent=`${plural(locations.length,'porte affichée')} · ${locations.filter(location=>keyById.get(location.keyId).rarity==='epic').length} / 11 violettes · ${plural(mapBuildings().length,'bâtiment activé')}`;
    document.querySelectorAll('.room-row[data-key]').forEach(button=>{const active=button.dataset.key===selectedKeyId;button.setAttribute('aria-pressed',String(active));button.classList.toggle('active',active);const check=button.parentElement.querySelector('.toggle-key');if(check)check.checked=keyIsShown(keyById.get(button.dataset.key));});
    document.querySelectorAll('.atlas-building-row').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.building===selected)));
  }
  function keyIdentityHtml(key){
    return `<div class="key-identity"><img class="key-icon-large" src="${escape(key.icon)}" alt="${escape(key.displayNameFr)}"><div><strong class="key-name">${escape(key.displayNameFr)}</strong><p class="room-location">${escape(key.rarityLabelFr)} · ${escape(key.nameEn)}<br>${escape(keyPlace(key.id))}</p></div></div><p class="key-meta">Description pour reconnaître la bonne clé :</p><blockquote class="key-description">${escape(key.descriptionFr)}</blockquote>`;
  }
  function updateRoomUI(){
    const room=currentRoom(),b=byId.get(selected),key=keyById.get(selectedKeyId),bar=$('floor-bar'),card=$('room-detail');
    bar.replaceChildren();bar.hidden=!b?.floors.length;card.hidden=!key;
    $('sidebar-eyebrow').textContent='ATLAS DE LOOTY BAY · TOUS LES QUARTIERS';
    $('sidebar-title').textContent='Carte complète';
    document.querySelector('.intro').textContent='Recherche une clé par son nom ou sa description. Affiche les bâtiments et les repères dont tu as besoin.';
    if(!b){
      $('location-district').textContent='DOWNTOWN · SUNNY BEACH · LORAINE HILLS · PALMSIDE';
      $('location-title').textContent=searchQuery?`Recherche : ${searchQuery}`:'Toute la ville, tous les accès';
      $('location-subtitle').textContent='Les portes et les bâtiments restent disponibles indépendamment du parcours duo. Clique pour ouvrir un plan.';
      $('building-summary').innerHTML='<div><strong>28 intérieurs documentés · 11 portes violettes · 33 clés identifiées.</strong><br><span>L’hôpital est repéré, mais aucun plan intérieur vérifiable n’est disponible.</span></div>';
      if(key)card.innerHTML=keyIdentityHtml(key)+'<p>La clé est identifiée, mais aucun emplacement précis n’est disponible.</p>';
      return;
    }
    const f=currentFloor(b);
    $('location-district').textContent=b.district.toUpperCase()+ (key?' · '+key.rarityLabelFr.toUpperCase():'');
    $('location-title').textContent=b.name.replace(' — clé 7','');
    $('location-subtitle').textContent=!f?'Bâtiment repéré. Le plan intérieur n’est pas fourni par les sources consultées.':room?`${f.label} · ${room.floorLevel===floorLevel?room.descriptionFr:'La salle sélectionnée se trouve à un autre étage.'}`:`${f.label} · ${f.targets.length} cibles principales documentées. Les filtres agissent sur ce plan et sur toute la carte.`;
    for(const floor of b.floors){const button=document.createElement('button');button.type='button';button.setAttribute('aria-pressed',String(floor.level===floorLevel));button.textContent=`${floor.label}${room&&floor.level===room.floorLevel?' · salle sélectionnée':''}`;button.addEventListener('click',()=>selectRoomFloor(floor.level));bar.append(button);}
    if(key){
      card.classList.toggle('is-legendary',key.rarity==='legendary');let details='';
      if(room){
        const outside=room.outsideSmallSafes.map(safe=>`<button type="button" data-key-open="safe_key_${safe.key}">${escape(keyName('safe_key_'+safe.key))} — ${escape(keyPlace('safe_key_'+safe.key))}</button>`).join('');
        details=`<div class="room-metrics"><div><strong>${room.drillCount}</strong><span>grand${room.drillCount>1?'s':''} coffre${room.drillCount>1?'s':''}</span></div><div><strong>${room.furnitureCount}</strong><span>meubles</span></div><div><strong>${room.securedComputerCount}</strong><span>PC sécurisé</span></div><div><strong>${room.smallSafeCount}</strong><span>petit coffre</span></div></div><div class="room-kit"><strong>Matériel pour cette salle</strong><p>${escape(key.displayNameFr)} ci-dessus<br><b>${plural(room.drillCount,'mini-perceuse')} (Mini-foret / Mini Drill)</b><br>Outil USB pour l’ordinateur</p></div>${outside?`<div class="room-exterior"><strong>Petit coffre ailleurs dans le bâtiment</strong>${outside}</div>`:''}<button type="button" class="object-close" id="whole-building">Voir tout le bâtiment</button>`;
      }else{
        const isSafe=key.family==='safe_key';details=`<div class="room-kit"><strong>${isSafe?'Cette clé ouvre le petit coffre indiqué.':'Cette clé ouvre la porte indiquée.'}</strong><p>${isSafe?'La cible est sélectionnée sur le plan.':'Le plan affiche l’étage complet ; le contenu de cette salle n’est pas isolé dans le comptage.'}</p></div>`;
      }
      card.innerHTML=keyIdentityHtml(key)+details+`<p class="room-source"><a href="${escape(key.sourceUrls[0])}" target="_blank" rel="noopener noreferrer">Fiche de la clé et description</a> · repères vérifiés le 17/11/2026</p>`;
      card.querySelectorAll('[data-key-open]').forEach(button=>button.addEventListener('click',()=>selectKey(button.dataset.keyOpen)));
      $('whole-building')?.addEventListener('click',()=>selectBuilding(b.id,floorLevel));
    }
    if(!f){$('building-summary').innerHTML='<strong>Emplacement du bâtiment connu · aucun intérieur inventé.</strong>';return;}
    const targets=room?b.floors.flatMap(f=>f.targets).filter(t=>room.targetIds.includes(t.id)):f.targets;
    $('building-summary').innerHTML=`<div><strong>${room?'Salle sélectionnée':escape(f.label)} : ${plural(targets.filter(t=>t.kind==='furniture').length,'meuble')} · ${plural(targets.filter(t=>t.kind==='drill').length,'grand coffre')} · ${plural(targets.filter(t=>t.kind==='small').length,'petit coffre')}${targets.some(t=>t.kind==='deposit')?' · '+plural(targets.filter(t=>t.kind==='deposit').length,'casier bancaire'):''}${targets.some(t=>t.kind==='computer')?' · '+targets.filter(t=>t.kind==='computer').length+' PC':''}.</strong><br><span>Somme du barème si chaque repère est crédité une fois. Le vidage complet peut déclencher plusieurs actions.</span></div><div class="summary-points">${sumPoints(targets)} pts <small>base de calcul</small></div>`;
  }
  function toolName(id){return keyById.has(id)?`${keyName(id)} — ${keyPlace(id)}`:({mini_drill_1:'Mini-perceuse / Mini-foret (Mini Drill)',drill_1:'Foreuse bancaire (Drill)',usb_1_cumulative:'Outil de piratage USB',lockpick_1:'Crochet'}[id]||id);}
  function showObject(b,f,t,type='target'){
    if(b&&selected!==b.id){selected=b.id;floorLevel=f.level;selectedRoom=null;selectedKeyId=null;}
    if(!b){selected=null;selectedRoom=null;selectedKeyId=null;}
    if(f)floorLevel=f.level;updateUI();selectedTarget=t.id;
    const box=$('object-detail');box.hidden=false;box.style.borderLeftColor=colorLight[t.kind]||'#7dd4ec';
    const isExtra=type==='loot'||type==='security'||type==='access',isComputer=t.kind==='computer',rule=rulesByType.get(t.baseType);
    let action=t.kind==='furniture'?'Fouille ce meuble.':t.kind==='drill'?`Ouvre ce coffre avec : ${toolName(t.drillItem||'mini_drill_1')}.`:t.kind==='small'?(t.keyId?`Clé requise : ${toolName(t.keyId)}.`:'Aucune clé requise n’est indiquée pour ce petit coffre dans la configuration.'):t.kind==='deposit'?'Casier de dépôt bancaire : repère à fouiller après avoir accédé à la salle.':t.kind==='atm'?'Distributeur à braquer, repéré dans la configuration des actions caméra.':isComputer?'Garde l’outil de piratage USB sur toi pour enregistrer les données du PC.':type==='access'?'Accès verrouillé : consulte le matériel requis ci-dessous.':type==='security'?'Équipement de sécurité repéré sur le plan.':'Objet ou emplacement de butin du plan. Le contenu disponible dépend de la partie.';
    const required=[...new Set([...(t.requiredItems||[]),...(t.drillItem?[t.drillItem]:[])])];
    const keyButtons=required.filter(id=>keyById.has(id)).map(id=>`<button type="button" class="object-key-link" data-key-open="${escape(id)}">Voir ${escape(toolName(id))}</button>`).join('');
    const containing=rooms.find(room=>room.targetIds.includes(t.id)),access=containing?`Accès à la salle : ${keyName('room_key_'+containing.key)} — ${keyPlace('room_key_'+containing.key)}.`:'';
    const gainText=isComputer?`+${t.usbPoints||'?'} USB`:isExtra?'Repère':`${gainBadge(t)} pt${gain(t)>1?'s':''}`;
    const proof=isComputer?'Points USB séparés. Aucun gain caméra attribué à ce PC dans cette carte.':isExtra?'Aucun gain caméra attribué à ce repère dans la configuration consultée.':`<strong>${gainBadge(t)} caméra par action créditée.</strong> Valeur issue de la configuration de ce type d’objet.${t.kind==='furniture'?'<br>Le nombre de crédits pendant le vidage complet d’un meuble n’est pas exposé : ce +1 ne garantit pas un seul point pour toute la commode.':''}`;
    const source=t.sourceUrls?.find(url=>url.includes('robrun.info'))||t.sourceUrl||b?.sourceUrl||'https://robrun.info/map/';
    box.innerHTML=`<div class="object-heading"><div><h3>${escape(t.label||t.sourceLabel)}</h3><p class="object-place">${escape(b?b.name:'Distributeur de Looty Bay')}${f?' · '+escape(f.label):''}${t.n?' · repère '+t.n:''}</p></div><span class="object-gain" style="color:${colorLight[t.kind]||'#7dd4ec'}">${gainText}</span></div><p class="plan-status">${isComputer?'Outil USB':isExtra?'Repère du plan':'Gain par action · configuration publiée'}</p><p class="object-action">${action}</p><div class="point-proof">${proof}</div>${required.length?`<p class="object-access"><strong>Matériel :</strong> ${required.map(id=>escape(toolName(id))).join(' ; ')}</p>`:''}${keyButtons}${access?`<p class="object-access">${escape(access)}</p>`:''}${rule?`<p class="object-place">Type : ${escape(rule.labelFr)}</p>`:''}<p class="room-source"><a href="${escape(source.includes('/map/data.js')?'https://robrun.info/map/':source)}" target="_blank" rel="noopener noreferrer">Source du repère</a></p><button type="button" class="object-close">Fermer le détail</button>`;
    box.querySelectorAll('[data-key-open]').forEach(button=>button.addEventListener('click',()=>selectKey(button.dataset.keyOpen)));
    wireObjectClose();queueDraw();
  }
  function wireObjectClose(){const box=$('object-detail');box.querySelector('.object-close').addEventListener('click',()=>{box.hidden=true;selectedTarget=null;queueDraw();});if(window.innerWidth>650)box.scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'nearest'});}
  function initPointRules(){
    const grouped=new Map();for(const rule of pointRules.types){const label=rule.groupFr||rule.labelFr;grouped.set(label+'|'+rule.points,{label,points:rule.points});}
    $('point-rules-content').innerHTML=`<p><strong>Barème de la caméra violette · notoriété 3 · capacité 70.</strong></p><table><thead><tr><th>Type d’objet</th><th>Points / action</th></tr></thead><tbody>${[...grouped.values()].map(rule=>`<tr><td>${escape(rule.label)}</td><td>+${rule.points}</td></tr>`).join('')}</tbody></table><p>${escape(pointRules.noteFr)}</p><p>Les totaux de la carte supposent une action créditée par repère. Ils ne fixent pas le total obtenu en vidant entièrement un meuble.</p><p><a href="https://robrun.info/map/" target="_blank" rel="noopener noreferrer">Configuration et carte sources</a> · 34 types, 208 repères avec récompense caméra.</p>`;
  }

  function initList(){
    $('building-list').replaceChildren();
    $('total-points').textContent=String(buildings.reduce((sum,b)=>sum+planPoints(b),0));
    $('building-count').textContent=`${buildings.length} bâtiments`;
    document.querySelector('.intro').textContent=includeDrills?'35 meubles + 7 grands coffres par secteur : 70 points si chaque repère est crédité une fois. Arrêtez-vous à la jauge pleine.':'35 meubles par secteur, sans mini-perceuse. Base indicative : une action créditée par repère.';
    $('mode-split').setAttribute('aria-pressed',String(routeMode==='split'));
    $('mode-together').setAttribute('aria-pressed',String(routeMode==='together'));
    $('route-legend-text').textContent=routeMode==='split'?'A violet · B bleu':'1 → 12 · A violet / B bleu';
    $('budget-note').innerHTML=includeDrills?
      '<strong>14 mini-perceuses · 252 000 $ si achetées</strong><p>Budget maximal de ce parcours, 7 par joueur. Hypothèse : une action créditée par repère. Des crédits supplémentaires par meuble permettent d’arrêter plus tôt.</p>':
      '<strong>Sans perçage : base de 70 points</strong><p>35 meubles par secteur. Le gain réel dépend du nombre d’actions créditées ; surveillez vos deux jauges.</p>';
    for(const district of ['Downtown','Sunny Beach']){
      const bs=routeOrder().map(id=>byId.get(id)).filter(b=>b.district===district),player=owner(bs[0]);const section=document.createElement('section');section.className='district-group';section.style.setProperty('--circuit',player==='A'?'#c1a0f0':'#7dd4ec');
      const header=document.createElement('div');header.className='district-label';header.innerHTML=`<span>Joueur ${player} · ${escape(district)}</span><span>${bs.reduce((s,b)=>s+planPoints(b),0)} pts de base</span>`;section.append(header);
      const access=document.createElement('p');access.className='district-access';access.textContent=`${includeDrills?'7 mini-perceuses au maximum.':'Meubles uniquement.'} Clique sur les portes pour reconnaître les clés par leur nom et description.`;section.append(access);
      for(const b of bs){
        const button=document.createElement('button');button.type='button';button.className='building-button';button.dataset.building=b.id;button.setAttribute('aria-pressed','false');
        const drillCount=plannedDrills(b),note=isPharmacy(b)?'Meubles · coffre ignoré':`${b.furnitureCount} meubles${drillCount?' + '+drillCount+' coffre'+(drillCount>1?'s':''):''}`;
        button.innerHTML=`<span class="order">${stopLabel(b)}</span><span class="name">${escape(b.name.replace(' Sunny Beach','').replace(' Downtown',''))}<small>${escape(note)}</small></span><span class="points">${planPoints(b)}<small>pts</small></span>`;
        button.addEventListener('click',()=>{selectBuilding(b.id);if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});});section.append(button);
      }
      $('building-list').append(section);
    }
  }
  function initBaseMap(){
    const palette={sea:'#68b5be',sand:'#e0dbc4',ground:'#faf4e3',decor:'#e4e1d1',road_outline:'#f0ebd9',road_main:'#91958b',road_minor:'#c2c0ae',road_side:'#ccc9b5',marking:'#f6f2e4',monorail:'#b7b3a5',pool:'#73c4ca',buildings:'#e0d7b8'};
    const group=$('map-base');
    group.append(el('rect',{x:-1800,y:-1800,width:3600,height:3600,fill:palette.sea}));
    for(const layer of window.CAMERA_MAP_LAYERS){
      const attrs={d:layer.d,fill:palette[layer.kind]||palette.ground};
      if(layer.kind==='buildings'){attrs.stroke='#b9b197';attrs['stroke-width']=.25;}
      group.append(el('path',attrs));
    }
  }
  function updateUI(){
    document.body.dataset.view=viewMode;
    updateAtlasStats();
    $('view-doors').setAttribute('aria-pressed',String(viewMode==='doors'));
    $('view-routes').setAttribute('aria-pressed',String(viewMode==='routes'));
    $('view-plants').setAttribute('aria-pressed',String(viewMode==='plants'));
    $('view-trash').setAttribute('aria-pressed',String(viewMode==='trash'));
    $('trash-panel').hidden=viewMode!=='trash';$('quick-trash').checked=layers.trash;
    $('trash-quick-count').textContent=`${trashPoints.length} emplacements · affichables avec les plantes`;
    document.querySelector('.plant-header-info').innerHTML=viewMode==='trash'?`<span>●</span> ${trashPoints.length} poubelles`:'<span>●</span> Plantes · sans clé';
    $('quick-plants').checked=viewMode==='plants';$('plant-panel').hidden=viewMode!=='plants';
    $('object-detail').hidden=true;
    if(viewMode==='trash'){updateTrashUI();return;}
    if(viewMode==='plants'){updatePlantUI();return;}
    if(viewMode==='doors'||selected&&!buildings.some(b=>b.id===selected)){updateRoomUI();return;}
    $('room-detail').hidden=true;
    $('sidebar-eyebrow').textContent='DUO · DEUX CAMÉRAS VIOLETTES';
    $('sidebar-title').textContent='Parcours caméras';
    document.querySelectorAll('.building-button').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.building===selected)));
    $('object-detail').hidden=true;
    const b=byId.get(selected),bar=$('floor-bar');bar.replaceChildren();
    if(!b){
      $('location-district').textContent='DOWNTOWN + SUNNY BEACH';
      $('location-title').textContent=includeDrills?(routeMode==='split'?'Deux circuits · base de 70 points chacun':'Ensemble · 12 étapes pour 2 caméras'):'Sans perceuse · base de 70 points';
      $('location-subtitle').textContent=routeMode==='split'?'Ce mode vous sépare : A suit le violet, B suit le bleu. Chacun fouille ses propres cibles.':'Restez ensemble : A fouille Downtown, B fouille Sunny Beach. Le pont relie les deux secteurs.';bar.hidden=true;
      $('building-summary').innerHTML=`<strong>${includeDrills?'Arrêtez chacun à 70 points sur votre jauge. Les totaux supposent une action créditée par repère.':'35 meubles par secteur : total réel à lire sur vos jauges, selon les actions créditées.'}</strong><span>Trait plein : rues · Pointillés : approche indicative.</span>`;return;
    }
    const f=currentFloor(b);
    $('location-district').textContent=`ARRÊT ${stopLabel(b)} · JOUEUR ${owner(b)} · ${b.district.toUpperCase()}`;$('location-title').textContent=b.name;
    $('location-subtitle').textContent=b.id==='GasStation'?'Sous-sol : boîtier bleu ELEVATOR sur le pont élévateur du Service Center.':isPharmacy(b)?'Fouille les 7 meubles. Le grand coffre est facultatif : il est exclu des 70 points du plan.':'Fouille les cibles colorées. Les cibles grisées sont des bonus hors plan.';
    bar.hidden=false;
    for(const floor of b.floors){const button=document.createElement('button');button.type='button';button.setAttribute('aria-pressed',String(floor.level===floorLevel));button.textContent=`${floor.label} · ${floorPoints(b,floor)} pts du plan`;button.addEventListener('click',()=>selectBuilding(b.id,floor.level));bar.append(button);}
    const access=document.createElement('span');access.className='access-summary';access.textContent=`${keyLocations.filter(location=>location.b.id===b.id&&location.kind==='door').length} porte(s) à clé : clique sur leur repère pour identifier la clé.`;bar.append(access);
    $('building-summary').innerHTML=`<div><strong>Joueur ${owner(b)} : ${b.furnitureCount} meubles${plannedDrills(b)?' + '+plannedDrills(b)+' grands coffres':''}</strong><br><span>${isPharmacy(b)?'Ne percez ce coffre qu’en appoint si des points manquent.':'Clés et cibles créditables nécessaires. Bonus gris non comptés.'}</span></div><div class="summary-points">${planPoints(b)} pts <small>base du plan</small></div>`;
  }
  function selectTarget(b,f,t){showObject(b,f,t);}

  $('overview').addEventListener('click',()=>overview());
  $('view-doors').addEventListener('click',()=>setMode('doors'));
  $('view-routes').addEventListener('click',()=>setMode('routes'));
  $('view-plants').addEventListener('click',()=>setMode('plants'));
  $('view-trash').addEventListener('click',()=>setMode('trash'));
  $('trash-city').addEventListener('click',()=>{trashQuery='';$('trash-search').value='';setMode('trash');if(window.innerWidth<=650)$('map-stage').scrollIntoView({behavior:reduceMotion?'auto':'smooth',block:'center'});});
  $('trash-search').addEventListener('input',event=>{trashQuery=event.target.value;overview(false);});
  window.addEventListener('hashchange',()=>{const mode=location.hash==='#plantes'?'plants':location.hash==='#poubelles'?'trash':null;if(mode&&viewMode!==mode)setMode(mode);else if(!mode&&['plants','trash'].includes(viewMode))setMode('doors');});
  $('quick-plants').addEventListener('change',event=>setMode(event.target.checked?'plants':'doors'));
  $('plant-sector').addEventListener('change',event=>{plantSector=Object.hasOwn(plantData.sectors,event.target.value)?event.target.value:'all';savePlants();overview();});
  $('plant-extra').addEventListener('change',event=>{plantExtra=event.target.checked;savePlants();overview();});
  $('plant-reset').addEventListener('click',()=>{for(const id of Object.keys(plantData.stops))plantDone.delete(id);savePlants();overview();});
  $('plant-source-links').innerHTML=plantData.sources.map(source=>`<li><a href="${escape(source.url)}" target="_blank" rel="noopener noreferrer">${escape(source.label)}</a></li>`).join('');
  document.querySelectorAll('[data-layer]').forEach(input=>input.addEventListener('change',()=>{
    const name=input.dataset.layer;layers[name]=input.checked;
    if(name==='trash'&&!input.checked&&viewMode==='trash'){setMode('doors');return;}
    if(input.checked&&['purple','gold','otherKeys','small'].includes(name))for(const key of keyCatalog)if(keyLayer(key)===name)hiddenKeyIds.delete(key.id);
    savePreferences();syncFilters();updateUI();queueDraw();
  }));
  $('show-all-layers').addEventListener('click',()=>{for(const key of Object.keys(layers))layers[key]=true;hiddenKeyIds.clear();hiddenBuildingIds.clear();savePreferences();syncFilters();initRoomList();updateUI();queueDraw();});
  $('hide-all-layers').addEventListener('click',()=>{for(const key of Object.keys(layers))layers[key]=false;savePreferences();syncFilters();initRoomList();updateUI();queueDraw();});
  $('map-search').addEventListener('input',event=>{searchQuery=event.target.value;initRoomList();$('keys-section').open=true;overview(false);});
  $('map-search').addEventListener('keydown',event=>{if(event.key==='Enter'){event.preventDefault();const matches=keyCatalog.filter(matchesKey);if(matches.length===1)selectKey(matches[0].id);else overview();}});
  $('district-filter').addEventListener('change',event=>{districtFilter=event.target.value;initRoomList();overview();});
  for(const mode of ['split','together'])$('mode-'+mode).addEventListener('click',()=>{routeMode=mode;layers.route=true;syncFilters();initList();overview();savePreferences();});
  $('include-drills').addEventListener('change',event=>{includeDrills=event.target.checked;initList();updateUI();queueDraw();});
  $('zoom-in').addEventListener('click',()=>zoom(1.5));$('zoom-out').addEventListener('click',()=>zoom(1/1.5));
  $('fit-building').addEventListener('click',()=>selected?(viewMode==='doors'?selectRoomFloor(floorLevel):selectBuilding(selected,floorLevel)):overview());
  svg.addEventListener('wheel',e=>{e.preventDefault();zoom(Math.exp(-Math.max(-120,Math.min(120,e.deltaY))*.0025),point(e));},{passive:false});
  svg.addEventListener('dblclick',e=>{e.preventDefault();zoom(1.8,point(e));});
  svg.addEventListener('pointerdown',e=>{
    if(e.button!==0&&e.pointerType!=='touch')return;
    cancelAnimationFrame(animation);pointers.set(e.pointerId,point(e));
    clickSuppressed=false;
    if(pointers.size===1)gesture={view:{...view},start:point(e),moved:false};
    if(pointers.size===2){const [a,b]=[...pointers.values()];gesture={view:{...view},center:[(a[0]+b[0])/2,(a[1]+b[1])/2],distance:Math.hypot(a[0]-b[0],a[1]-b[1]),moved:true};clickSuppressed=true;}
    if(pointers.size===2)for(const id of pointers.keys())svg.setPointerCapture(id);
  });
  svg.addEventListener('pointermove',e=>{
    if(!pointers.has(e.pointerId)||!gesture)return;pointers.set(e.pointerId,point(e));const r=rect();
    if(pointers.size>=2){
      const [a,b]=[...pointers.values()],center=[(a[0]+b[0])/2,(a[1]+b[1])/2],distance=Math.hypot(a[0]-b[0],a[1]-b[1]);
      if(!gesture.center)return;
      const w=Math.max(4,Math.min(2600,gesture.view.w*gesture.distance/Math.max(distance,1))),h=w*r.height/r.width;
      const world=[gesture.view.x+gesture.center[0]/r.width*gesture.view.w,gesture.view.y+gesture.center[1]/r.height*gesture.view.h];
      setView({x:world[0]-center[0]/r.width*w,y:world[1]-center[1]/r.height*h,w,h});clickSuppressed=true;svg.classList.add('dragging');
    }else if(gesture.start){
      const p=point(e),dx=p[0]-gesture.start[0],dy=p[1]-gesture.start[1];
      if(Math.hypot(dx,dy)>5||gesture.moved){gesture.moved=true;clickSuppressed=true;if(!svg.hasPointerCapture(e.pointerId))svg.setPointerCapture(e.pointerId);svg.classList.add('dragging');setView({...gesture.view,x:gesture.view.x-dx/r.width*gesture.view.w,y:gesture.view.y-dy/r.height*gesture.view.h});}
    }
  });
  function pointerEnd(e){
    pointers.delete(e.pointerId);if(svg.hasPointerCapture(e.pointerId))svg.releasePointerCapture(e.pointerId);
    if(pointers.size===1){const p=[...pointers.values()][0];gesture={view:{...view},start:p,moved:true};}
    else if(pointers.size===0){gesture=null;svg.classList.remove('dragging');setTimeout(()=>{clickSuppressed=false;},50);}
  }
  svg.addEventListener('pointerup',pointerEnd);svg.addEventListener('pointercancel',pointerEnd);
  svg.addEventListener('keydown',e=>{
    if(e.target!==svg)return;
    if(e.key==='+'||e.key==='='){e.preventDefault();zoom(1.4);}else if(e.key==='-'){e.preventDefault();zoom(1/1.4);}else if(e.key==='Home'){e.preventDefault();overview();}else if(['ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(e.key)){e.preventDefault();const v={...view};if(e.key==='ArrowLeft')v.x-=v.w*.12;if(e.key==='ArrowRight')v.x+=v.w*.12;if(e.key==='ArrowUp')v.y-=v.h*.12;if(e.key==='ArrowDown')v.y+=v.h*.12;setView(v);}
  });
  initBaseMap();initList();initRoomList();initPointRules();syncFilters();
  let firstSize=true;
  new ResizeObserver(()=>{
    const r=rect();if(r.width<1||r.height<1)return;
    if(firstSize){firstSize=false;overview(false);}
    else {const target=animationTarget||view;const h=target.w*r.height/r.width;setView({...target,y:target.y+(target.h-h)/2,h});}
  }).observe($('map-stage'));
})();
