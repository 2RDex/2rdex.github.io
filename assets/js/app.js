(() => {
const $=id=>document.getElementById(id);
let ctx=null, master=null, autoGainNode=null, analyser=null, loudnessAnalyser=null, loudnessData=null, kHighPass=null, kShelf=null, eqNodes=[], output=null;
let originalLoudnessAnalyser=null, originalLoudnessData=null, originalKHighPass=null, originalKShelf=null;
let processedLoudnessAnalyser=null, processedLoudnessData=null, processedKHighPass=null, processedKShelf=null;
const LOUDNESS_HISTORY_POINTS=72; // 72 samples × 400 ms = 28.8 seconds
let originalSmoothedLufs=null, processedSmoothedLufs=null, compareHistory=Array.from({length:LOUDNESS_HISTORY_POINTS},()=>({original:null,processed:null})), lastCompareSampleAt=0, compareLastSignalAt=0;
let inputLevelAnalyser=null,inputLevelData=null;
let outputSplitter=null,outputLeftAnalyser=null,outputRightAnalyser=null,outputLeftData=null,outputRightData=null;
let speakerRoutes=[null,null], defaultOutputConnected=true, knownOutputDevices=[], knownInputDevices=[], outputPermissionPrimed=false, outputPermissionRequestActive=false;
const MAX_BROWSER_SOURCES=5;
let browserSources=[],isStartingBrowser=false,nextBrowserSourceId=1;
const isFirefox=/Firefox\//i.test(navigator.userAgent)&&!/Seamonkey\//i.test(navigator.userAgent);
let sounds=[],peak=-Infinity,raf=0,smoothedLufs=null,fastSmoothedLufs=null,lastMeterAt=0,lastSignalAt=0,lastGainUpdate=0,currentAutoGainDb=0;
let loudnessTrend=[],fadeOutProtection=false,fadeOutReferenceLufs=null,silenceStartedAt=0;
const freqs=[31,63,125,250,500,1000,2000,4000,8000,16000];
const defaults={eq:Array(10).fill(0),eqEnabled:true,autoEnabled:true,autoTarget:-16,autoMaxBoost:12,outputGain:0};
const AUTO_SETTINGS_KEY='pat-auto-settings-v1';
let autoSaveTimer=null;
let autoSettingsRestored=false;
const speakerDefaults=[{enabled:false,deviceId:'',deviceLabel:'',delay:0,gain:0},{enabled:false,deviceId:'',deviceLabel:'',delay:0,gain:0}];
let speakerSettings=loadSpeakerSettings();
function toast(s){const t=$('toast');t.textContent=s;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),2300)}
function db(v){return v<=0.00001?'−∞':(20*Math.log10(v)).toFixed(1)}

function loadSpeakerSettings(){
 try{
  const saved=JSON.parse(localStorage.getItem('pat-speakers')||'null');
  if(!saved||!Array.isArray(saved.slots))return {enabled:false,slots:speakerDefaults.map(s=>({...s}))};
  return {enabled:!!saved.enabled,slots:speakerDefaults.map((d,i)=>({...d,...(saved.slots[i]||{})}))};
 }catch{return {enabled:false,slots:speakerDefaults.map(s=>({...s}))}}
}
function saveSpeakerSettings(){
 localStorage.setItem('pat-speakers',JSON.stringify(speakerSettings));
}
function loadAutoSettings(){
 try{
  const raw=localStorage.getItem(AUTO_SETTINGS_KEY);
  if(!raw)return null;
  const saved=JSON.parse(raw);
  if(!saved||typeof saved!=='object')return null;
  const clamp=(value,min,max,fallback)=>{
   const n=Number(value);return Number.isFinite(n)?Math.min(max,Math.max(min,n)):fallback;
  };
  return {
   eq:freqs.map((_,i)=>Math.round(clamp(saved.eq?.[i],-12,12,defaults.eq[i])*2)/2),
   eqEnabled:typeof saved.eqEnabled==='boolean'?saved.eqEnabled:defaults.eqEnabled,
   autoEnabled:typeof saved.autoEnabled==='boolean'?saved.autoEnabled:defaults.autoEnabled,
   autoTarget:clamp(saved.autoTarget,-24,-10,defaults.autoTarget),
   autoMaxBoost:clamp(saved.autoMaxBoost,0,18,defaults.autoMaxBoost),
   outputGain:clamp(saved.outputGain,-18,12,defaults.outputGain)
  };
 }catch(e){return null}
}
function setAutoSaveStatus(message,failed=false){
 const el=$('autoSaveStatus');if(!el)return;
 el.textContent=message;el.classList.toggle('error',failed);
}
function saveAutoSettings(immediate=false){
 if(!autoSettingsRestored)return;
 if(autoSaveTimer){clearTimeout(autoSaveTimer);autoSaveTimer=null;}
 const write=()=>{
  autoSaveTimer=null;
  try{
   localStorage.setItem(AUTO_SETTINGS_KEY,JSON.stringify(state()));
   setAutoSaveStatus('บันทึกการตั้งค่าแล้ว');
  }catch(e){
   setAutoSaveStatus('บันทึกไม่ได้ · พื้นที่จัดเก็บไม่พร้อม',true);
  }
 };
 setAutoSaveStatus('กำลังบันทึก...');
 if(immediate)write();else autoSaveTimer=setTimeout(write,180);
}
function restoreAutoSettings(){
 const saved=loadAutoSettings();
 apply(saved||defaults,false);
 autoSettingsRestored=true;
 setAutoSaveStatus(saved?'โหลดการตั้งค่าล่าสุดแล้ว':'เริ่มต้นการบันทึกอัตโนมัติ');
}
function speakerEl(i,suffix){return $('speaker'+i+suffix)}
function createSpeakerRoute(i){
 if(speakerRoutes[i]||!ctx)return speakerRoutes[i];
 const delay=ctx.createDelay(1);
 const gain=ctx.createGain();
 const destination=ctx.createMediaStreamDestination();
 const audio=new Audio();
 audio.autoplay=true;audio.playsInline=true;audio.className='audio-output-element';audio.setAttribute('aria-hidden','true');
 audio.srcObject=destination.stream;
 document.body.append(audio);
 delay.delayTime.value=Number(speakerSettings.slots[i].delay||0)/1000;
 gain.gain.value=0;
 analyser.connect(delay);delay.connect(gain);gain.connect(destination);
 speakerRoutes[i]={delay,gain,destination,audio,deviceId:''};
 return speakerRoutes[i];
}
function connectDefaultOutput(shouldConnect){
 if(!ctx||!analyser)return;
 if(shouldConnect&&!defaultOutputConnected){analyser.connect(ctx.destination);defaultOutputConnected=true}
 else if(!shouldConnect&&defaultOutputConnected){try{analyser.disconnect(ctx.destination)}catch{}defaultOutputConnected=false}
}
async function startSpeakerPlayback(i){
 const route=speakerRoutes[i];if(!route)return;
 try{
  if(ctx&&ctx.state==='suspended')await ctx.resume();
  await route.audio.play();
 }catch(e){
  toast('เบราว์เซอร์ยังไม่อนุญาตให้เริ่ม Output นี้ กดลองทดสอบเสียงอีกครั้ง');
 }
}
function startActiveSpeakerOutputs(){
 if(!speakerSettings.enabled)return;
 speakerSettings.slots.forEach((s,i)=>{
  if(s.enabled&&s.deviceId&&speakerRoutes[i])startSpeakerPlayback(i);
 });
}
function updateSpeakerRouting(){
 if(!ctx||!analyser)return;
 const active=speakerSettings.enabled&&speakerSettings.slots.some((s,i)=>s.enabled&&s.deviceId&&speakerRoutes[i]);
 connectDefaultOutput(!active);
 speakerSettings.slots.forEach((s,i)=>{
  const route=speakerRoutes[i];if(!route)return;
  const on=!!(active&&s.enabled&&s.deviceId&&route.deviceId===s.deviceId);
  const linear=on?Math.pow(10,Number(s.gain||0)/20):0;
  route.gain.gain.setTargetAtTime(linear,ctx.currentTime,.035);
  $('speakerSlot'+i).classList.toggle('active',on);
  $('speaker'+i+'Test').disabled=!s.deviceId;
 });
}
async function requestTemporaryMicrophoneAccess(deviceId=null){
 if(!navigator.mediaDevices?.getUserMedia)throw new Error('เบราว์เซอร์ไม่รองรับการขอสิทธิ์อุปกรณ์เสียง');
 let temporaryStream=null;
 try{
  const audio=deviceId?{deviceId:{exact:deviceId}}:true;
  temporaryStream=await navigator.mediaDevices.getUserMedia({audio,video:false});
  // Stop every capture track immediately. The stream is never connected to the Audio Engine.
  temporaryStream.getTracks().forEach(track=>track.stop());
  temporaryStream=null;
  outputPermissionPrimed=true;
  return true;
 }finally{
  if(temporaryStream)temporaryStream.getTracks().forEach(track=>track.stop());
 }
}
async function refreshOutputDevices(){
 const support=$('speakerSupport');
 if(!navigator.mediaDevices?.enumerateDevices){support.textContent='เบราว์เซอร์ไม่รองรับการตรวจหาอุปกรณ์';return}
 try{
  const devices=await navigator.mediaDevices.enumerateDevices();
  knownOutputDevices=devices.filter(d=>d.kind==='audiooutput');
  knownInputDevices=devices.filter(d=>d.kind==='audioinput');
  [0,1].forEach(i=>{
   const select=speakerEl(i,'Device'),current=speakerSettings.slots[i].deviceId;
   const previousLabel=speakerSettings.slots[i].deviceLabel;
   select.innerHTML='';
   const placeholder=document.createElement('option');placeholder.value='';placeholder.textContent='เลือกอุปกรณ์...';select.append(placeholder);
   knownOutputDevices.forEach(d=>{
    const option=document.createElement('option');option.value=d.deviceId;
    option.textContent=d.label||(d.deviceId==='default'?'ลำโพงเริ่มต้นของระบบ':'อุปกรณ์เสียงที่อนุญาต');
    select.append(option);
   });
   if(current&&knownOutputDevices.some(d=>d.deviceId===current)){
    select.value=current;
   }else if(current&&!outputPermissionPrimed){
    // Before permission, browsers may expose only the default sink. Do not discard saved choices.
    select.value='';
    speakerEl(i,'Status').textContent='กดแสดงรายชื่ออุปกรณ์เพื่อปลดล็อก';
    speakerEl(i,'Status').classList.remove('connected');
   }else if(current){
    select.value='';
    speakerSettings.slots[i].enabled=false;
    speakerEl(i,'Enabled').checked=false;
    speakerEl(i,'Status').textContent=previousLabel?`ไม่พบอุปกรณ์: ${previousLabel}`:'อุปกรณ์ไม่พร้อมใช้งาน';
    speakerEl(i,'Status').classList.remove('connected');
    if(speakerRoutes[i]){
     speakerRoutes[i].gain.gain.setTargetAtTime(0,ctx?.currentTime||0,.03);
     speakerRoutes[i].audio.pause();
     speakerRoutes[i].deviceId='';
    }
   }
  });
  const restore=[];
  speakerSettings.slots.forEach((s,i)=>{
   const device=knownOutputDevices.find(d=>d.deviceId===s.deviceId);
   if(device&&s.deviceId&&(!speakerRoutes[i]||speakerRoutes[i].deviceId!==s.deviceId)){
    restore.push(applySpeakerDevice(i,s.deviceId,device.label||s.deviceLabel,false));
   }
  });
  if(restore.length)await Promise.all(restore);
  updateSpeakerRouting();
  if(!outputPermissionPrimed&&knownOutputDevices.length<=1){
   support.textContent='กด “แสดงอุปกรณ์เสียง” เพื่ออนุญาตชั่วคราวและแสดง Output ทั้งหมด';
  }else{
   support.textContent=knownOutputDevices.length?`พบอุปกรณ์ Output ${knownOutputDevices.length} รายการ`:'ไม่พบอุปกรณ์ Output';
  }
  saveSpeakerSettings();
 }catch(e){
  support.textContent=`อ่านรายชื่ออุปกรณ์ไม่สำเร็จ: ${e.message}`;
 }
}
async function unlockAndRefreshOutputDevices(){
 if(outputPermissionRequestActive)return;
 if(!window.isSecureContext){
  toast('ต้องเปิดผ่าน localhost หรือ HTTPS จึงจะขอสิทธิ์อุปกรณ์เสียงได้');
  return;
 }
 outputPermissionRequestActive=true;
 const button=$('refreshOutputs');
 const oldText=button.textContent;
 button.disabled=true;button.textContent='กำลังแสดงอุปกรณ์...';
 $('speakerSupport').textContent='กำลังขอสิทธิ์ไมโครโฟนชั่วคราว...';
 try{
  await requestTemporaryMicrophoneAccess();
  await refreshOutputDevices();
  toast('หยุดไมโครโฟนแล้ว · อัปเดตรายชื่อ Output สำเร็จ');
 }catch(e){
  const reason=e.name==='NotAllowedError'?'ไม่ได้รับอนุญาตให้ใช้ไมโครโฟนชั่วคราว':e.name==='NotFoundError'?'ไม่พบไมโครโฟนสำหรับปลดล็อกรายชื่อ Output':`ปลดล็อกรายชื่ออุปกรณ์ไม่สำเร็จ: ${e.message}`;
  $('speakerSupport').textContent=reason;
  toast(reason);
 }finally{
  button.disabled=false;button.textContent=oldText;outputPermissionRequestActive=false;
 }
}
async function authorizeOutputGroup(outputDevice){
 if(!outputDevice?.groupId)return false;
 const matchingInput=knownInputDevices.find(d=>d.kind==='audioinput'&&d.groupId===outputDevice.groupId&&d.deviceId);
 if(!matchingInput)return false;
 await requestTemporaryMicrophoneAccess(matchingInput.deviceId);
 const refreshed=await navigator.mediaDevices.enumerateDevices();
 knownInputDevices=refreshed.filter(d=>d.kind==='audioinput');
 knownOutputDevices=refreshed.filter(d=>d.kind==='audiooutput');
 return true;
}
async function applySpeakerDevice(i,deviceId,label,playNow=false){
 const s=speakerSettings.slots[i];
 if(deviceId&&speakerSettings.slots.some((other,j)=>j!==i&&other.deviceId===deviceId)){
  toast('อุปกรณ์นี้ถูกเลือกไว้กับลำโพงอีกช่องแล้ว');speakerEl(i,'Device').value=s.deviceId||'';return false;
 }
 if(!deviceId){
  s.deviceId='';s.deviceLabel='';
  if(speakerRoutes[i]){speakerRoutes[i].deviceId='';speakerRoutes[i].gain.gain.setTargetAtTime(0,ctx?.currentTime||0,.03);speakerRoutes[i].audio.pause()}
  speakerEl(i,'Status').textContent='ยังไม่ได้เลือกอุปกรณ์';speakerEl(i,'Status').classList.remove('connected');
  saveSpeakerSettings();updateSpeakerRouting();return true;
 }
 ensureAudio();
 const route=createSpeakerRoute(i);
 const outputDevice=knownOutputDevices.find(d=>d.deviceId===deviceId);
 try{
  if(typeof route.audio.setSinkId!=='function')throw new Error('เบราว์เซอร์ไม่รองรับ HTMLMediaElement.setSinkId()');
  const sinkId=deviceId==='default'?'':deviceId;
  try{
   await route.audio.setSinkId(sinkId);
  }catch(firstError){
   if(firstError.name!=='NotAllowedError')throw firstError;
   // A microphone permission grants output access only for a device in the same group.
   const authorized=await authorizeOutputGroup(outputDevice);
   if(!authorized)throw new Error('Output นี้ยังไม่ได้รับสิทธิ์ และไม่พบไมโครโฟนที่จับคู่กับอุปกรณ์นี้');
   await route.audio.setSinkId(sinkId);
  }
  route.deviceId=deviceId;s.deviceId=deviceId;s.deviceLabel=label||outputDevice?.label||'Audio Output';
  speakerEl(i,'Device').value=deviceId;speakerEl(i,'Status').textContent=s.deviceLabel;speakerEl(i,'Status').classList.add('connected');
  speakerEl(i,'Test').disabled=false;
  saveSpeakerSettings();updateSpeakerRouting();
  if(playNow&&s.enabled&&speakerSettings.enabled)await startSpeakerPlayback(i);
  return true;
 }catch(e){
  const message=e.name==='NotAllowedError'?'ไม่ได้รับสิทธิ์ให้ส่งเสียงไปยัง Output นี้':e.message.includes('ไม่พบไมโครโฟน')?e.message:`ตั้งค่า Output ไม่สำเร็จ: ${e.message}`;
  toast(message);
  s.deviceId='';s.deviceLabel='';route.deviceId='';
  speakerEl(i,'Device').value='';speakerEl(i,'Status').textContent='เลือกอุปกรณ์ไม่สำเร็จ';speakerEl(i,'Status').classList.remove('connected');
  saveSpeakerSettings();updateSpeakerRouting();return false;
 }
}
async function chooseSpeakerOutput(i){
 await unlockAndRefreshOutputDevices();
 speakerEl(i,'Device').focus();
}
function setSpeakerControls(i){
 const s=speakerSettings.slots[i];
 speakerEl(i,'Enabled').checked=!!s.enabled;
 speakerEl(i,'Delay').value=String(s.delay??0);
 speakerEl(i,'DelayValue').textContent=`${s.delay??0} ms`;
 speakerEl(i,'Gain').value=String(s.gain??0);
 speakerEl(i,'GainValue').textContent=`${Number(s.gain??0)>0?'+':''}${Number(s.gain??0)} dB`;
 speakerEl(i,'Status').textContent=s.deviceLabel||'ยังไม่ได้เลือกอุปกรณ์';
 if(s.deviceLabel)speakerEl(i,'Status').classList.add('connected');
}
function initialiseSpeakerUI(){
 $('speakersEnabled').checked=!!speakerSettings.enabled;
 [0,1].forEach(i=>{
  setSpeakerControls(i);
  speakerEl(i,'Enabled').addEventListener('change',()=>{
   const s=speakerSettings.slots[i];
   if(speakerEl(i,'Enabled').checked&&!s.deviceId){speakerEl(i,'Enabled').checked=false;toast('กรุณาเลือกอุปกรณ์เสียงก่อนเปิดลำโพง');return}
   s.enabled=speakerEl(i,'Enabled').checked;
   if(s.enabled){speakerSettings.enabled=true;$('speakersEnabled').checked=true}
   saveSpeakerSettings();
   if(s.enabled&&s.deviceId&&!speakerRoutes[i]){
    const device=knownOutputDevices.find(d=>d.deviceId===s.deviceId);
    applySpeakerDevice(i,s.deviceId,device?.label||s.deviceLabel,true);
   }
   updateSpeakerRouting();
   if(s.enabled&&speakerRoutes[i])startSpeakerPlayback(i);
  });
  speakerEl(i,'Device').addEventListener('change',async e=>{
   const id=e.target.value;const found=knownOutputDevices.find(d=>d.deviceId===id);
   await applySpeakerDevice(i,id,found?.label||'',true);
  });
  speakerEl(i,'Choose').addEventListener('click',()=>chooseSpeakerOutput(i));
  speakerEl(i,'Delay').addEventListener('input',e=>{
   const val=Number(e.target.value);speakerSettings.slots[i].delay=val;speakerEl(i,'DelayValue').textContent=`${val} ms`;
   if(speakerRoutes[i])speakerRoutes[i].delay.delayTime.setTargetAtTime(val/1000,ctx.currentTime,.03);
   saveSpeakerSettings();
  });
  speakerEl(i,'Gain').addEventListener('input',e=>{
   const val=Number(e.target.value);speakerSettings.slots[i].gain=val;speakerEl(i,'GainValue').textContent=`${val>0?'+':''}${val} dB`;
   saveSpeakerSettings();updateSpeakerRouting();
  });
  speakerEl(i,'Test').addEventListener('click',()=>testSpeaker(i));
 });
 $('speakersEnabled').addEventListener('change',()=>{
  speakerSettings.enabled=$('speakersEnabled').checked;
  if(speakerSettings.enabled&&!speakerSettings.slots.some((s,i)=>s.enabled&&s.deviceId)){
   const first=speakerSettings.slots.findIndex(s=>s.deviceId);
   if(first>=0){speakerSettings.slots[first].enabled=true;speakerEl(first,'Enabled').checked=true}
   else{speakerSettings.enabled=false;$('speakersEnabled').checked=false;toast('เลือกอุปกรณ์เสียงก่อนเปิด Multi-Speaker')}
  }
  saveSpeakerSettings();updateSpeakerRouting();
  if(speakerSettings.enabled)speakerSettings.slots.forEach((s,i)=>{
   if(s.enabled&&s.deviceId&&!speakerRoutes[i]){
    const device=knownOutputDevices.find(d=>d.deviceId===s.deviceId);
    if(device)applySpeakerDevice(i,s.deviceId,device.label||s.deviceLabel,true);
   }else if(s.enabled&&s.deviceId&&speakerRoutes[i])startSpeakerPlayback(i);
  });
 });
 $('refreshOutputs').addEventListener('click',unlockAndRefreshOutputDevices);
 $('speakerTest').addEventListener('click',testAllSpeakers);
 refreshOutputDevices();
 if(navigator.mediaDevices?.addEventListener)navigator.mediaDevices.addEventListener('devicechange',refreshOutputDevices);
 else if(navigator.mediaDevices)navigator.mediaDevices.ondevicechange=refreshOutputDevices;
}
function testTone(targetRoute=null){
 ensureAudio();ctx.resume();
 const osc=ctx.createOscillator(),gain=ctx.createGain();osc.type='sine';osc.frequency.value=660;gain.gain.value=.0001;
 osc.connect(gain);
 if(targetRoute)gain.connect(targetRoute.delay);else gain.connect(analyser);
 const now=ctx.currentTime;gain.gain.setValueAtTime(.0001,now);gain.gain.exponentialRampToValueAtTime(.12,now+.025);gain.gain.setValueAtTime(.12,now+.14);gain.gain.exponentialRampToValueAtTime(.0001,now+.22);
 osc.start(now);osc.stop(now+.24);
}
function testSpeaker(i){
 const s=speakerSettings.slots[i],route=speakerRoutes[i];
 if(!route||!s.deviceId){toast('เลือกอุปกรณ์ลำโพงก่อนทดสอบ');return}
 if(!speakerSettings.enabled){speakerSettings.enabled=true;$('speakersEnabled').checked=true}
 if(!s.enabled){s.enabled=true;speakerEl(i,'Enabled').checked=true}
 updateSpeakerRouting();startSpeakerPlayback(i);testTone(route);toast(`ทดสอบลำโพง ${i+1}`);
}
function testAllSpeakers(){
 const active=speakerSettings.slots.filter((s,i)=>s.enabled&&s.deviceId&&speakerRoutes[i]);
 if(!active.length){toast('เลือกและเปิดใช้งานลำโพงอย่างน้อยหนึ่งตัวก่อน');return}
 ensureAudio();if(!speakerSettings.enabled){speakerSettings.enabled=true;$('speakersEnabled').checked=true}
 updateSpeakerRouting();speakerSettings.slots.forEach((s,i)=>{if(s.enabled&&s.deviceId&&speakerRoutes[i])startSpeakerPlayback(i)});testTone();toast('ส่งเสียงทดสอบไปยังลำโพงที่เปิดอยู่');
}

function ensureAudio(){
 if(ctx)return;
 ctx=new (window.AudioContext||window.webkitAudioContext)({latencyHint:'interactive'});
 master=ctx.createGain();master.gain.value=1;
 autoGainNode=ctx.createGain();autoGainNode.gain.value=1;
 // K-weighting approximation for perceptual loudness estimation (not a certified EBU R128 meter).
 kHighPass=ctx.createBiquadFilter();kHighPass.type='highpass';kHighPass.frequency.value=38.135;kHighPass.Q.value=.5;
 kShelf=ctx.createBiquadFilter();kShelf.type='highshelf';kShelf.frequency.value=1681.974;kShelf.gain.value=4;kShelf.Q.value=.707;
 loudnessAnalyser=ctx.createAnalyser();loudnessAnalyser.fftSize=8192;loudnessAnalyser.smoothingTimeConstant=0;loudnessData=new Float32Array(loudnessAnalyser.fftSize);
 originalKHighPass=ctx.createBiquadFilter();originalKHighPass.type='highpass';originalKHighPass.frequency.value=38.135;originalKHighPass.Q.value=.5;
 originalKShelf=ctx.createBiquadFilter();originalKShelf.type='highshelf';originalKShelf.frequency.value=1681.974;originalKShelf.gain.value=4;originalKShelf.Q.value=.707;
 originalLoudnessAnalyser=ctx.createAnalyser();originalLoudnessAnalyser.fftSize=8192;originalLoudnessAnalyser.smoothingTimeConstant=0;originalLoudnessData=new Float32Array(originalLoudnessAnalyser.fftSize);
 processedKHighPass=ctx.createBiquadFilter();processedKHighPass.type='highpass';processedKHighPass.frequency.value=38.135;processedKHighPass.Q.value=.5;
 processedKShelf=ctx.createBiquadFilter();processedKShelf.type='highshelf';processedKShelf.frequency.value=1681.974;processedKShelf.gain.value=4;processedKShelf.Q.value=.707;
 processedLoudnessAnalyser=ctx.createAnalyser();processedLoudnessAnalyser.fftSize=8192;processedLoudnessAnalyser.smoothingTimeConstant=0;processedLoudnessData=new Float32Array(processedLoudnessAnalyser.fftSize);
 eqNodes=freqs.map((f,i)=>{const n=ctx.createBiquadFilter();n.type=i===0?'lowshelf':i===9?'highshelf':'peaking';n.frequency.value=f;n.Q.value=1;n.gain.value=0;return n});
 output=ctx.createGain();analyser=ctx.createAnalyser();analyser.fftSize=2048;analyser.smoothingTimeConstant=.82;
 inputLevelAnalyser=ctx.createAnalyser();inputLevelAnalyser.fftSize=2048;inputLevelAnalyser.smoothingTimeConstant=0;inputLevelData=new Float32Array(inputLevelAnalyser.fftSize);
 outputSplitter=ctx.createChannelSplitter(2);
 outputLeftAnalyser=ctx.createAnalyser();outputLeftAnalyser.fftSize=2048;outputLeftAnalyser.smoothingTimeConstant=0;outputLeftData=new Float32Array(outputLeftAnalyser.fftSize);
 outputRightAnalyser=ctx.createAnalyser();outputRightAnalyser.fftSize=2048;outputRightAnalyser.smoothingTimeConstant=0;outputRightData=new Float32Array(outputRightAnalyser.fftSize);
 analyser.connect(outputSplitter);outputSplitter.connect(outputLeftAnalyser,0);outputSplitter.connect(outputRightAnalyser,1);
 master.connect(eqNodes[0]);
 let chain=[...eqNodes,autoGainNode,output,analyser];chain.slice(1).forEach((n,i)=>chain[i].connect(n));
 analyser.connect(ctx.destination);defaultOutputConnected=true;
 // Compare the untouched input with the final processed signal using matching K-weighted meter branches.
 master.connect(originalKHighPass);originalKHighPass.connect(originalKShelf);originalKShelf.connect(originalLoudnessAnalyser);
 output.connect(processedKHighPass);processedKHighPass.connect(processedKShelf);processedKShelf.connect(processedLoudnessAnalyser);
 // This separate tap measures the equalized signal before Auto Gain and is used by the gain controller.
 eqNodes[eqNodes.length-1].connect(kHighPass);kHighPass.connect(kShelf);kShelf.connect(loudnessAnalyser);
 $('sampleRate').textContent=(ctx.sampleRate/1000).toFixed(1)+' kHz';
 updateProcessing();draw();
}
function formatDbfs(value){
 return Number.isFinite(value)?`${value.toFixed(1)} dBFS`:'−∞ dBFS';
}
function resetLiveMeters(){
 peak=-Infinity;
 $('inputDbReadout').innerHTML='−∞ <small>dBFS</small>';
 $('dbReadout').innerHTML='−∞ <small>dBFS</small>';
 $('peakReadout').textContent='−∞ dBFS';
 $('outputLeftValue').textContent='−∞ dBFS';
 $('outputRightValue').textContent='−∞ dBFS';
 $('outputLeftBar').style.width='0%';
 $('outputRightBar').style.width='0%';
 $('monitorState').textContent='WAITING FOR AUDIO';
 $('monitorState').classList.remove('active');
}
function measureWaveform(analyserNode,data){
 if(!analyserNode||!data)return {rms:0,peak:0,rmsDb:-Infinity,peakDb:-Infinity};
 analyserNode.getFloatTimeDomainData(data);
 let sum=0,maxAbs=0;
 for(let i=0;i<data.length;i++){
  const sample=data[i],abs=Math.abs(sample);
  sum+=sample*sample;
  if(abs>maxAbs)maxAbs=abs;
 }
 const rms=Math.sqrt(sum/data.length);
 return {
  rms,peak:maxAbs,
  rmsDb:rms>0?20*Math.log10(rms):-Infinity,
  peakDb:maxAbs>0?20*Math.log10(maxAbs):-Infinity
 };
}
function meterWidth(dbfs){
 if(!Number.isFinite(dbfs))return '0%';
 return `${Math.max(0,Math.min(100,(dbfs+60)/60*100))}%`;
}
function updateLiveMeters(){
 if(!inputLevelAnalyser||!analyser||!outputLeftAnalyser||!outputRightAnalyser)return;
 const input=measureWaveform(inputLevelAnalyser,inputLevelData);
 const left=measureWaveform(outputLeftAnalyser,outputLeftData);
 const right=measureWaveform(outputRightAnalyser,outputRightData);
 const outputRms=Math.sqrt((left.rms*left.rms+right.rms*right.rms)/2);
 const outputRmsDb=outputRms>0?20*Math.log10(outputRms):-Infinity;
 const outputPeakDb=Math.max(left.peakDb,right.peakDb);
 $('inputDbReadout').innerHTML=`${formatDbfs(input.rmsDb).replace(' dBFS','')} <small>dBFS</small>`;
 $('dbReadout').innerHTML=`${formatDbfs(outputRmsDb).replace(' dBFS','')} <small>dBFS</small>`;
 $('outputLeftValue').textContent=formatDbfs(left.rmsDb);
 $('outputRightValue').textContent=formatDbfs(right.rmsDb);
 $('outputLeftBar').style.width=meterWidth(left.rmsDb);
 $('outputRightBar').style.width=meterWidth(right.rmsDb);
 if(Number.isFinite(outputPeakDb))peak=Math.max(peak,outputPeakDb);
 $('peakReadout').textContent=formatDbfs(peak);
 const hasInput=Number.isFinite(input.rmsDb)&&browserSources.length>0;
 $('monitorState').textContent=hasInput?'LIVE MONITORING':'WAITING FOR AUDIO';
 $('monitorState').classList.toggle('active',!!hasInput);
}
function connectSource(stream){
 ensureAudio();
 const node=ctx.createMediaStreamSource(stream),gain=ctx.createGain();
 gain.gain.value=1;
 node.connect(gain);
 gain.connect(master);
 // Meter-only branch: this analyser does not alter or feed back into the audio signal.
 gain.connect(inputLevelAnalyser);
 return {node,gain};
}
function resetBrowserLoudness(){
 smoothedLufs=null;fastSmoothedLufs=null;lastMeterAt=0;lastSignalAt=0;lastGainUpdate=0;currentAutoGainDb=0;
 loudnessTrend=[];fadeOutProtection=false;fadeOutReferenceLufs=null;silenceStartedAt=0;
 originalSmoothedLufs=null;processedSmoothedLufs=null;
 compareHistory=Array.from({length:LOUDNESS_HISTORY_POINTS},()=>({original:null,processed:null}));
 lastCompareSampleAt=0;compareLastSignalAt=0;
 $('originalLufs').textContent='— LUFS';$('processedLufs').textContent='— LUFS';$('loudnessDelta').textContent='— dB';
 $('inputLufs').textContent='— LUFS';$('autoGainReadout').textContent='0.0 dB';
 drawLoudnessComparison();
 if(autoGainNode&&ctx)autoGainNode.gain.setTargetAtTime(1,ctx.currentTime,.25);
}
function updateBrowserButton(starting=isStartingBrowser){
 const button=$('browserBtn'),count=browserSources.length,full=count>=MAX_BROWSER_SOURCES;
 const unavailable=isFirefox||!navigator.mediaDevices?.getDisplayMedia;
 button.disabled=starting||full||unavailable;
 button.classList.toggle('is-sharing',count>0);
 button.setAttribute('aria-pressed',String(count>0));
 button.textContent=starting?'กำลังเปิดหน้าต่างเลือกแท็บ...':full?`ครบ ${MAX_BROWSER_SOURCES} แท็บแล้ว`:'＋ เพิ่ม Browser Tab';
 $('stopAllBrowsers').disabled=count===0;
 if(isFirefox)$('browserStatus').textContent='Firefox ไม่รองรับการจับเสียงแท็บผ่านเว็บแอป';
 else if(!navigator.mediaDevices?.getDisplayMedia)$('browserStatus').textContent='เบราว์เซอร์นี้ไม่รองรับ Tab Capture';
 else if(starting&&count)$('browserStatus').textContent=`รับเสียง ${count} แท็บ · กำลังเพิ่มแท็บใหม่`;
 else if(starting)$('browserStatus').textContent='กรุณาเลือกแท็บและเปิดแชร์เสียง';
 else if(count)$('browserStatus').textContent=`กำลังรับเสียง ${count} แท็บ`;
 else $('browserStatus').textContent='ยังไม่ได้เชื่อมต่อ';
 $('browserStatus').classList.toggle('connected',count>0);
 $('browserCount').textContent=`${count} / ${MAX_BROWSER_SOURCES}`;
}
function renderBrowserSources(){
 const root=$('browserSources');root.innerHTML='';
 browserSources.forEach(source=>{
  const row=document.createElement('div');row.className='browser-source-item';row.dataset.sourceId=String(source.id);
  const top=document.createElement('div');top.className='browser-source-top';
  const info=document.createElement('div');info.className='browser-source-info';
  const name=document.createElement('strong');name.className='browser-source-name';name.textContent=source.label;name.title=source.label;
  const state=document.createElement('small');state.className='browser-source-state';state.textContent=source.muted?'ปิดเสียงอยู่':'กำลังรับเสียง';
  info.append(name,state);
  const actions=document.createElement('div');actions.className='browser-source-controls';
  const mute=document.createElement('button');mute.type='button';mute.className='ghost small browser-source-mute';mute.textContent=source.muted?'เปิดเสียง':'ปิดเสียง';mute.setAttribute('aria-pressed',String(source.muted));mute.addEventListener('click',()=>{
   source.muted=!source.muted;source.gain.gain.setTargetAtTime(source.muted?0:Math.pow(10,source.gainDb/20),ctx.currentTime,.025);renderBrowserSources();
  });
  const remove=document.createElement('button');remove.type='button';remove.className='ghost small browser-source-remove';remove.textContent='✕';remove.title='นำแท็บนี้ออก';remove.setAttribute('aria-label',`นำ ${source.label} ออก`);remove.addEventListener('click',()=>removeBrowserSource(source.id));
  actions.append(mute,remove);top.append(info,actions);
  const gainLine=document.createElement('div');gainLine.className='browser-source-gain';
  const gainLabel=document.createElement('label');gainLabel.textContent='GAIN';gainLabel.htmlFor=`browserGain${source.id}`;
  const slider=document.createElement('input');slider.id=`browserGain${source.id}`;slider.type='range';slider.min='-24';slider.max='12';slider.step='1';slider.value=String(source.gainDb);slider.disabled=source.muted;slider.setAttribute('aria-label',`Gain ${source.label}`);
  const value=document.createElement('b');value.textContent=`${source.gainDb>0?'+':''}${source.gainDb} dB`;
  slider.addEventListener('input',()=>{source.gainDb=Number(slider.value);value.textContent=`${source.gainDb>0?'+':''}${source.gainDb} dB`;if(!source.muted)source.gain.gain.setTargetAtTime(Math.pow(10,source.gainDb/20),ctx.currentTime,.025)});
  gainLine.append(gainLabel,slider,value);row.append(top,gainLine);root.append(row);source.row=row;
 });
 updateBrowserButton();updateCount();
}
async function startBrowser(){
 if(isStartingBrowser)return;
 if(browserSources.length>=MAX_BROWSER_SOURCES){toast(`เพิ่มได้สูงสุด ${MAX_BROWSER_SOURCES} แท็บ`);return}
 if(isFirefox){toast('Firefox ไม่รองรับการจับเสียงแท็บผ่านเว็บแอป');return}
 isStartingBrowser=true;updateBrowserButton(true);
 try{
  ensureAudio();startActiveSpeakerOutputs();
  // Call getDisplayMedia immediately from this click handler to preserve transient user activation.
  const capturePromise=navigator.mediaDevices.getDisplayMedia({
   video:true,
   audio:{
    suppressLocalAudioPlayback:true,
    echoCancellation:false,
    noiseSuppression:false,
    autoGainControl:false,
    channelCount:{ideal:2}
   }
  });
  if(ctx.state==='suspended')await ctx.resume().catch(()=>{});
  const stream=await capturePromise;
  if(!stream.getAudioTracks().length){stream.getTracks().forEach(t=>t.stop());toast('แท็บนี้ไม่ได้ส่งเสียงมาให้ กรุณาเลือกแชร์เสียงแท็บด้วย');return}
  const wasEmpty=browserSources.length===0;
  const videoTrack=stream.getVideoTracks()[0];
  const sourceId=nextBrowserSourceId++;
  // Show the exact capture track label supplied by the browser, including opaque
  // labels such as web-contents-media-stream://... when that is what it exposes.
  const trackLabel=(videoTrack?.label||'').trim();
  const label=trackLabel||`Browser Tab ${sourceId}`;
  const connected=connectSource(stream);
  const source={id:sourceId,stream,node:connected.node,gain:connected.gain,label,gainDb:0,muted:false,removing:false,row:null};
  browserSources.push(source);
  if(wasEmpty){peak=-Infinity;resetLiveMeters();resetBrowserLoudness()}
  stream.getTracks().forEach(track=>track.addEventListener('ended',()=>{
   if(!source.removing)removeBrowserSource(source.id,true);
  },{once:true}));
  renderBrowserSources();
  toast(`เชื่อมต่อ ${label} แล้ว`);
 }catch(e){
  if(e.name==='NotAllowedError')toast('ยกเลิกการแชร์แท็บ');
  else toast('ไม่สามารถรับเสียงจากแท็บได้: '+e.message);
 }finally{
  isStartingBrowser=false;updateBrowserButton();
 }
}
function removeBrowserSource(id,ended=false,silent=false){
 const index=browserSources.findIndex(source=>source.id===id);
 if(index<0)return;
 const [source]=browserSources.splice(index,1);source.removing=true;
 try{source.node.disconnect()}catch{}
 try{source.gain.disconnect()}catch{}
 source.stream.getTracks().forEach(track=>{if(track.readyState==='live')track.stop()});
 source.row?.remove();
 updateBrowserButton();updateCount();
 if(browserSources.length===0)resetLiveMeters();
 if(!silent){
  if(ended)toast(`การแชร์ ${source.label} สิ้นสุดแล้ว`);
  else toast(`นำ ${source.label} ออกแล้ว`);
 }
}
function stopBrowser(){
 [...browserSources].forEach(source=>removeBrowserSource(source.id,false,true));
 resetLiveMeters();updateBrowserButton();updateCount();
 toast('หยุด Browser Audio ทุกแท็บแล้ว');
}
function updateCount(){
 const count=browserSources.length;
 $('inputCount').textContent=`${count} / ${MAX_BROWSER_SOURCES}`;
 $('browserCount').textContent=`${count} / ${MAX_BROWSER_SOURCES}`;
}
function updateProcessing(){
 if(!ctx)return;
 eqNodes.forEach((n,i)=>{n.gain.value=$('eqEnabled').checked?Number($('eq-'+i).value):0});
 output.gain.value=Math.pow(10,Number($('outputGain').value)/20);
 updateAutoGain();
}
function updateAutoGain(){
 const enabled=$('autoEnabled').checked;
 const maxBoost=Number($('autoMaxBoost').value);
 const target=Number($('autoTarget').value);
 $('autoTargetVal').textContent=(target<0?'−':'')+Math.abs(target)+' LUFS';
 $('autoMaxBoostVal').textContent='+'+maxBoost+' dB';
 if(!enabled){currentAutoGainDb=0;fastSmoothedLufs=null;loudnessTrend=[];fadeOutProtection=false;fadeOutReferenceLufs=null;silenceStartedAt=0;if(ctx&&autoGainNode)autoGainNode.gain.setTargetAtTime(1,ctx.currentTime,.65);$('autoGainReadout').textContent='0.0 dB';$('autoStatus').textContent='ปิดการปรับความดังอัตโนมัติ';$('autoStatus').parentElement.classList.remove('active');return}
 if(!ctx||!autoGainNode){$('autoStatus').textContent='เปิดระบบ · รอรับเสียง';return}
 $('autoStatus').textContent='เปิดระบบ · กำลังวิเคราะห์เสียง';$('autoStatus').parentElement.classList.add('active');
}
function readEstimatedLufs(analyserNode,data){
 if(!analyserNode||!data)return null;
 analyserNode.getFloatTimeDomainData(data);
 let sum=0;for(let i=0;i<data.length;i++)sum+=data[i]*data[i];
 const rms=Math.sqrt(sum/data.length);
 if(!Number.isFinite(rms)||rms<0.0005)return null;
 return -0.691+20*Math.log10(rms);
}
function smoothLufs(previous,current,dt){
 if(current===null)return previous;
 const alpha=1-Math.exp(-Math.max(1,Math.min(500,dt))/1800);
 return previous===null?current:previous+(current-previous)*alpha;
}
function drawLoudnessComparison(){
 const canvas=$('loudnessCompare');if(!canvas)return;
 const c=canvas.getContext('2d');
 const w=canvas.clientWidth,h=canvas.clientHeight,dpr=window.devicePixelRatio||1;
 if(!w||!h)return;
 if(canvas.width!==Math.floor(w*dpr)||canvas.height!==Math.floor(h*dpr)){canvas.width=Math.floor(w*dpr);canvas.height=Math.floor(h*dpr)}
 c.setTransform(dpr,0,0,dpr,0,0);c.clearRect(0,0,w,h);
 const left=34,right=10,top=10,bottom=19,plotW=w-left-right,plotH=h-top-bottom;
 const min=-36,max=-6;
 c.font='9px Inter, sans-serif';c.textAlign='right';c.textBaseline='middle';
 [-36,-30,-24,-18,-12,-6].forEach(v=>{
  const y=top+(max-v)/(max-min)*plotH;
  c.strokeStyle='#573149';c.lineWidth=1;c.beginPath();c.moveTo(left,y);c.lineTo(w-right,y);c.stroke();
  c.fillStyle='#B996AA';c.fillText(String(v),left-7,y);
 });
 const target=Number($('autoTarget')?.value??-16);
 if(target>=min&&target<=max){
  const y=top+(max-target)/(max-min)*plotH;
  c.save();c.setLineDash([4,4]);c.strokeStyle='#A57D92';c.lineWidth=1;c.beginPath();c.moveTo(left,y);c.lineTo(w-right,y);c.stroke();c.restore();
 }
 const drawLine=(key,color)=>{
  if(!compareHistory.length)return;
  c.strokeStyle=color;c.lineWidth=2;c.lineJoin='round';c.lineCap='round';c.beginPath();
  let drawing=false;
  compareHistory.forEach((point,index)=>{
   const value=point?.[key];
   if(!Number.isFinite(value)){
    drawing=false;
    return;
   }
   const x=left+(index/Math.max(1,LOUDNESS_HISTORY_POINTS-1))*plotW;
   const y=top+(max-Math.max(min,Math.min(max,value)))/(max-min)*plotH;
   if(!drawing)c.moveTo(x,y);else c.lineTo(x,y);
   drawing=true;
  });
  c.stroke();
 };
 drawLine('original','#D16F61');drawLine('processed','#F29AB9');
 c.textAlign='left';c.textBaseline='alphabetic';c.fillStyle='#B996AA';c.fillText('ก่อนเริ่ม',left,bottom+14);
 c.textAlign='right';c.fillText('ปัจจุบัน',w-right,bottom+14);
}
function updateLoudnessComparison(now){
 const dt=lastCompareSampleAt?Math.min(500,now-lastCompareSampleAt):100;
 const original=readEstimatedLufs(originalLoudnessAnalyser,originalLoudnessData);
 const processed=readEstimatedLufs(processedLoudnessAnalyser,processedLoudnessData);
 if(original!==null||processed!==null)compareLastSignalAt=now;
 if(compareLastSignalAt&&now-compareLastSignalAt>1400){
  originalSmoothedLufs=null;processedSmoothedLufs=null;
 }
 originalSmoothedLufs=smoothLufs(originalSmoothedLufs,original,dt);
 processedSmoothedLufs=smoothLufs(processedSmoothedLufs,processed,dt);
 if(originalSmoothedLufs!==null)$('originalLufs').textContent=originalSmoothedLufs.toFixed(1)+' LUFS';
 else $('originalLufs').textContent='— LUFS';
 if(processedSmoothedLufs!==null)$('processedLufs').textContent=processedSmoothedLufs.toFixed(1)+' LUFS';
 else $('processedLufs').textContent='— LUFS';
 if(originalSmoothedLufs!==null&&processedSmoothedLufs!==null){
  const delta=processedSmoothedLufs-originalSmoothedLufs;
  $('loudnessDelta').textContent=(delta>0?'+':'')+delta.toFixed(1)+' dB';
  $('loudnessDelta').classList.toggle('positive',delta>0.15);
  $('loudnessDelta').classList.toggle('negative',delta< -0.15);
 }else{
  $('loudnessDelta').textContent='— dB';
  $('loudnessDelta').classList.remove('positive','negative');
 }
 if(now-lastCompareSampleAt>=400){
  lastCompareSampleAt=now;
  compareHistory.shift();
  compareHistory.push({original:originalSmoothedLufs,processed:processedSmoothedLufs});
  drawLoudnessComparison();
 }
}

function updateLoudness(now){
 if(!loudnessAnalyser||!ctx)return;
 const data=loudnessData;loudnessAnalyser.getFloatTimeDomainData(data);
 let sum=0;for(let i=0;i<data.length;i++)sum+=data[i]*data[i];
 const rms=Math.sqrt(sum/data.length);

 // Treat very low-level audio as silence instead of trying to normalize its noise floor.
 // The brief confirmation window avoids resetting the controller on tiny dropouts.
 if(!Number.isFinite(rms)||rms<0.0007){
  $('inputLufs').textContent='— LUFS';
  if(!silenceStartedAt)silenceStartedAt=now;
  const silenceDuration=now-silenceStartedAt;
  if(silenceDuration>=120&&Math.abs(currentAutoGainDb)>0.05){
   currentAutoGainDb=0;
   if($('autoEnabled').checked&&autoGainNode)autoGainNode.gain.setTargetAtTime(1,ctx.currentTime,.35);
   $('autoGainReadout').textContent='0.0 dB';
  }
  if(silenceDuration>=420){
   smoothedLufs=null;fastSmoothedLufs=null;lastMeterAt=0;lastSignalAt=0;
   loudnessTrend=[];fadeOutProtection=false;fadeOutReferenceLufs=null;lastGainUpdate=0;
   if(!browserSources.length&&!sounds.some(s=>!s.audio.paused))$('autoStatus').textContent='รอรับเสียงเพื่อวิเคราะห์';
  }
  return;
 }
 silenceStartedAt=0;
 lastSignalAt=now;
 const instantLufs=-0.691+20*Math.log10(rms);
 const dt=lastMeterAt?Math.min(500,now-lastMeterAt):100;lastMeterAt=now;

 // Keep the normal control meter responsive while also tracking a faster envelope
 // for fade-out detection. A downward trend is latched until the signal recovers.
 const fastAlpha=1-Math.exp(-dt/420);
 fastSmoothedLufs=fastSmoothedLufs===null?instantLufs:fastSmoothedLufs+(instantLufs-fastSmoothedLufs)*fastAlpha;
 const slowAlpha=1-Math.exp(-dt/2500);
 smoothedLufs=smoothedLufs===null?instantLufs:smoothedLufs+(instantLufs-smoothedLufs)*slowAlpha;
 $('inputLufs').textContent=smoothedLufs.toFixed(1)+' LUFS';
 if(!$('autoEnabled').checked)return;
 if(now-lastGainUpdate<100)return;lastGainUpdate=now;

 loudnessTrend.push({time:now,lufs:fastSmoothedLufs});
 while(loudnessTrend.length&&now-loudnessTrend[0].time>2400)loudnessTrend.shift();
 if(!fadeOutProtection&&loudnessTrend.length>4&&now-loudnessTrend[0].time>=1400){
  const reference=Math.max(...loudnessTrend.map(sample=>sample.lufs));
  if(reference-fastSmoothedLufs>=4.5){
   fadeOutProtection=true;
   fadeOutReferenceLufs=reference;
  }
 }
 if(fadeOutProtection&&fadeOutReferenceLufs!==null&&fastSmoothedLufs>=fadeOutReferenceLufs-1.5){
  fadeOutProtection=false;
  fadeOutReferenceLufs=null;
  loudnessTrend=[];
  // Re-anchor the slow meter to the recovered signal so it cannot carry an
  // obsolete low fade-out reading into the next gain calculation.
  smoothedLufs=fastSmoothedLufs;
  $('autoStatus').textContent='เปิดระบบ · กำลังวิเคราะห์เสียง';
 }

 const target=Number($('autoTarget').value),maxBoost=Number($('autoMaxBoost').value);
 // During a detected fade-out, allow attenuation but never add positive gain.
 const requestedCorrection=Math.max(-18,Math.min(maxBoost,target-smoothedLufs));
 const correction=fadeOutProtection?Math.min(0,requestedCorrection):requestedCorrection;
 const linear=Math.pow(10,correction/20);
 autoGainNode.gain.setTargetAtTime(linear,ctx.currentTime,fadeOutProtection ? 0.6 : 0.9);
 currentAutoGainDb=correction;
 $('autoGainReadout').textContent=(correction>0?'+':'')+correction.toFixed(1)+' dB';
 if(fadeOutProtection)$('autoStatus').textContent='เปิดระบบ · ป้องกันการเร่งเสียงช่วง Fade Out';
 else $('autoStatus').textContent='เปิดระบบ · กำลังวิเคราะห์เสียง';
}

function formatEqDb(value){
 const n=Number(value);
 if(!Number.isFinite(n)||Math.abs(n)<0.0001)return '0 dB';
 const magnitude=Number.isInteger(Math.abs(n))?String(Math.abs(n)):String(Number(Math.abs(n).toFixed(1)));
 return (n>0?'+':'−')+magnitude+' dB';
}

function buildEQ(){
 const root=$('eqBands');root.innerHTML='';
 freqs.forEach((f,i)=>{const d=document.createElement('div');d.className='band';d.innerHTML=`<output id="eqval-${i}">${formatEqDb(0)}</output><input id="eq-${i}" aria-label="${f} Hz" type="range" min="-12" max="12" step=".5" value="0"><small>${f>=1000?(f/1000)+'k':f}</small>`;root.append(d);$('eq-'+i).addEventListener('input',()=>{ $('eqval-'+i).textContent=formatEqDb($('eq-'+i).value);updateProcessing();saveAutoSettings()})})
}
function bindRange(id,out,fmt){$(id).addEventListener('input',()=>{$(out).textContent=fmt($(id).value);updateProcessing();saveAutoSettings()})}
function draw(){
 if(!analyser)return;const canvas=$('spectrum'),c=canvas.getContext('2d'),data=new Uint8Array(analyser.frequencyBinCount);
 const render=()=>{raf=requestAnimationFrame(render);const now=performance.now();updateLoudness(now);updateLoudnessComparison(now);updateLiveMeters();const w=canvas.clientWidth,h=canvas.clientHeight,dpr=window.devicePixelRatio||1;if(canvas.width!==Math.floor(w*dpr)||canvas.height!==Math.floor(h*dpr)){canvas.width=w*dpr;canvas.height=h*dpr}c.setTransform(dpr,0,0,dpr,0,0);analyser.getByteFrequencyData(data);c.clearRect(0,0,w,h);
 c.strokeStyle='#573149';c.lineWidth=1;for(let y=1;y<5;y++){c.beginPath();c.moveTo(0,h*y/5);c.lineTo(w,h*y/5);c.stroke()}
 const bars=70,bw=w/bars,binHz=ctx.sampleRate/analyser.fftSize;
 let framePeak=0;for(let i=0;i<data.length;i++)if(data[i]>framePeak)framePeak=data[i];
 const signalActive=framePeak>2,minHz=30,maxHz=Math.min(18000,ctx.sampleRate*.45),ratio=maxHz/minHz;
 for(let i=0;i<bars;i++){
  const lowHz=minHz*Math.pow(ratio,i/bars),highHz=minHz*Math.pow(ratio,(i+1)/bars);
  const startBin=Math.max(1,Math.floor(lowHz/binHz));
  const endBin=Math.min(data.length,Math.max(startBin+1,Math.ceil(highHz/binHz)));
  let bandPeak=0;for(let bin=startBin;bin<endBin;bin++)if(data[bin]>bandPeak)bandPeak=data[bin];
  const v=bandPeak/255;
  const bh=signalActive?Math.max(v*(h-12),2):0;
  const grad=c.createLinearGradient(0,h-bh,0,h);grad.addColorStop(0,'#D66A9B');grad.addColorStop(1,'#F08CAF');
  c.fillStyle=grad;c.fillRect(i*bw+1,h-bh,Math.max(1,bw-3),bh);
 }
 };
 render();
}
function state(){return {eq:freqs.map((_,i)=>Number($('eq-'+i).value)),eqEnabled:$('eqEnabled').checked,autoEnabled:$('autoEnabled').checked,autoTarget:Number($('autoTarget').value),autoMaxBoost:Number($('autoMaxBoost').value),outputGain:Number($('outputGain').value)}}
function apply(s,save=true){freqs.forEach((_,i)=>{$('eq-'+i).value=s.eq?.[i]??0;$('eqval-'+i).textContent=formatEqDb($('eq-'+i).value)});$('eqEnabled').checked=s.eqEnabled??true;$('autoEnabled').checked=s.autoEnabled??true;$('autoTarget').value=s.autoTarget??-16;$('autoMaxBoost').value=s.autoMaxBoost??12;$('outputGain').value=s.outputGain??0;syncLabels();updateProcessing();if(save)saveAutoSettings(true)}
function syncLabels(){$('outputGainVal').textContent=$('outputGain').value+' dB';updateAutoGain()}

function presets(){return JSON.parse(localStorage.getItem('pat-presets')||'{}')}
function refreshPresets(){const s=$('presetSelect'),old=s.value;s.innerHTML='<option value="">เลือก Preset</option>';Object.keys(presets()).forEach(n=>{const o=document.createElement('option');o.value=n;o.textContent=n;s.append(o)});if(presets()[old])s.value=old}
$('browserBtn').onclick=startBrowser;
$('stopAllBrowsers').onclick=stopBrowser;
buildEQ();
$('eqEnabled').addEventListener('change',()=>{updateProcessing();saveAutoSettings(true)});
$('autoEnabled').addEventListener('change',()=>{updateProcessing();saveAutoSettings(true)});$('autoTarget').addEventListener('input',()=>{syncLabels();updateProcessing();saveAutoSettings()});$('autoMaxBoost').addEventListener('input',()=>{syncLabels();updateProcessing();saveAutoSettings()});
bindRange('outputGain','outputGainVal',v=>v+' dB');
$('eqReset').onclick=()=>{freqs.forEach((_,i)=>{$('eq-'+i).value=0;$('eqval-'+i).textContent=formatEqDb(0)});updateProcessing();saveAutoSettings(true)};
$('resetAll').onclick=()=>{apply(defaults);toast('คืนค่าเริ่มต้นแล้ว')};
$('savePreset').onclick=()=>{const name=prompt('ตั้งชื่อ Preset');if(!name?.trim())return;const p=presets();p[name.trim()]=state();localStorage.setItem('pat-presets',JSON.stringify(p));refreshPresets();$('presetSelect').value=name.trim();toast('บันทึก Preset แล้ว')};
$('loadPreset').onclick=()=>{const p=presets(),s=p[$('presetSelect').value];if(s){apply(s);toast('โหลด Preset แล้ว')}};
$('deletePreset').onclick=()=>{const n=$('presetSelect').value;if(!n)return;const p=presets();delete p[n];localStorage.setItem('pat-presets',JSON.stringify(p));refreshPresets();toast('ลบ Preset แล้ว')};
let currentSoundIndex=-1,playlistReturnFocus=null;
function formatTrackTime(seconds){
 if(!Number.isFinite(seconds)||seconds<0)return '--:--';
 const whole=Math.floor(seconds),minutes=Math.floor(whole/60),remaining=whole%60;
 return `${minutes}:${String(remaining).padStart(2,'0')}`;
}
function activeSound(){
 return currentSoundIndex>=0&&currentSoundIndex<sounds.length?sounds[currentSoundIndex]:null;
}
function updateSoundboardUI(){
 const current=activeSound();
 const playing=!!current&&!current.audio.paused;
 $('currentTrackTitle').textContent=current?current.file.name:'ยังไม่มีเพลง';
 $('currentTrackMeta').textContent=current
  ? `${playing?'กำลังเล่น':'พร้อมเล่น'} · TRACK ${currentSoundIndex+1} / ${sounds.length} · ${formatTrackTime(current.audio.duration)}`
  : 'เพิ่มไฟล์เสียงเพื่อเริ่ม Playlist';
 $('togglePlayback').textContent=playing?'Ⅱ':'▶';
 $('togglePlayback').setAttribute('aria-label',playing?'หยุดชั่วคราว':'เล่นเพลง');
 $('togglePlayback').title=playing?'หยุดชั่วคราว':'เล่นเพลง';
 $('togglePlayback').disabled=!current;
 $('previousTrack').disabled=sounds.length<2;
 $('nextTrack').disabled=sounds.length<2;
 $('playlistCount').textContent=String(sounds.length);
 $('playlistCountLabel').textContent=`${sounds.length} เพลง`;
 $('playlistFooterCount').textContent=`${sounds.length} TRACK${sounds.length===1?'':'S'}`;
 renderPlaylist();
}
function renderPlaylist(){
 const root=$('playlistItems');
 if(!sounds.length){
  root.innerHTML='<div class="playlist-empty"><span class="playlist-empty-icon">♫</span><strong>ยังไม่มีเพลงใน Playlist</strong><span>เพิ่มไฟล์ MP3, WAV หรือไฟล์เสียงที่ Browser รองรับ</span></div>';
  return;
 }
 root.innerHTML='';
 sounds.forEach((sound,index)=>{
  const isCurrent=index===currentSoundIndex;
  const isPlaying=isCurrent&&!sound.audio.paused;
  const row=document.createElement('div');
  row.className='playlist-track'+(isCurrent?' current':'');
  const select=document.createElement('button');
  select.className='playlist-track-select';
  select.type='button';
  select.setAttribute('aria-label',`เล่น ${sound.file.name}`);
  const indexLabel=document.createElement('span');
  indexLabel.className='playlist-track-index';
  indexLabel.textContent=isPlaying?'♫':String(index+1).padStart(2,'0');
  const info=document.createElement('span');
  info.className='playlist-track-info';
  const title=document.createElement('strong');
  title.textContent=sound.file.name;
  const subtitle=document.createElement('small');
  subtitle.textContent=`${isPlaying?'กำลังเล่น':isCurrent?'เลือกอยู่':'เพลงใน Playlist'} · ${formatTrackTime(sound.audio.duration)}`;
  info.append(title,subtitle);
  const playIcon=document.createElement('span');
  playIcon.className='playlist-track-play';
  playIcon.textContent=isPlaying?'Ⅱ':'▶';
  select.append(indexLabel,info,playIcon);
  select.addEventListener('click',()=>playSound(index,true));
  const remove=document.createElement('button');
  remove.className='playlist-track-remove';
  remove.type='button';
  remove.textContent='✕';
  remove.title='นำเพลงออกจาก Playlist';
  remove.setAttribute('aria-label',`ลบ ${sound.file.name}`);
  remove.addEventListener('click',()=>removeSound(index));
  row.append(select,remove);
  root.append(row);
 });
}
function openPlaylist(){
 playlistReturnFocus=document.activeElement;
 $('playlistModal').hidden=false;
 document.body.classList.add('playlist-open');
 $('playlistModal').querySelector('.playlist-dialog').focus();
 renderPlaylist();
}
function closePlaylist(){
 $('playlistModal').hidden=true;
 document.body.classList.remove('playlist-open');
 if(playlistReturnFocus&&typeof playlistReturnFocus.focus==='function')playlistReturnFocus.focus();
}
async function playSound(index,restart=false){
 if(index<0||index>=sounds.length)return;
 const target=sounds[index];
 try{
  ensureAudio();
  if(ctx.state==='suspended')await ctx.resume();
  startActiveSpeakerOutputs();
  sounds.forEach((sound,i)=>{if(i!==index&&!sound.audio.paused)sound.audio.pause()});
  if(!target.audio._source){
   target.audio._source=ctx.createMediaElementSource(target.audio);
   target.audio._source.connect(master);
  }
  if(restart||target.audio.ended)target.audio.currentTime=0;
  currentSoundIndex=index;
  await target.audio.play();
  updateSoundboardUI();
 }catch(error){
  toast(`เล่นไฟล์นี้ไม่ได้: ${error.message}`);
  updateSoundboardUI();
 }
}
function toggleSoundPlayback(){
 const current=activeSound();
 if(!current){
  if(sounds.length)playSound(0,true);
  return;
 }
 if(!current.audio.paused){
  current.audio.pause();
  updateSoundboardUI();
 }else{
  playSound(currentSoundIndex,current.audio.ended);
 }
}
function previousSound(){
 if(sounds.length<2)return;
 const current=activeSound();
 if(current&&current.audio.currentTime>3){
  current.audio.currentTime=0;
  if(current.audio.paused)updateSoundboardUI();
  return;
 }
 const previous=(currentSoundIndex-1+sounds.length)%sounds.length;
 playSound(previous,true);
}
function nextSound(){
 if(sounds.length<2)return;
 playSound((currentSoundIndex+1)%sounds.length,true);
}
function removeSound(index){
 if(index<0||index>=sounds.length)return;
 const removed=sounds[index];
 const wasCurrent=index===currentSoundIndex;
 removed.audio.pause();
 removed.audio.onended=null;
 if(removed.audio._source){
  try{removed.audio._source.disconnect()}catch{}
 }
 URL.revokeObjectURL(removed.url);
 sounds.splice(index,1);
 if(!sounds.length)currentSoundIndex=-1;
 else if(wasCurrent)currentSoundIndex=Math.min(index,sounds.length-1);
 else if(index<currentSoundIndex)currentSoundIndex--;
 updateSoundboardUI();
}
function addSoundFiles(fileList){
 const files=Array.from(fileList||[]).filter(file=>file.type.startsWith('audio/')||/\.(mp3|wav|flac|m4a|aac|ogg|opus|webm)$/i.test(file.name));
 if(!files.length){
  if(fileList?.length)toast('ไม่พบไฟล์เสียงที่รองรับ');
  return;
 }
 files.forEach(file=>{
  const url=URL.createObjectURL(file);
  const audio=new Audio(url);
  audio.controls=false;
  audio.preload='metadata';
  const sound={file,url,audio};
  sounds.push(sound);
  audio.addEventListener('loadedmetadata',()=>updateSoundboardUI(),{once:true});
  audio.addEventListener('error',()=>toast(`ไม่สามารถอ่านไฟล์ ${file.name} ได้`),{once:true});
  audio.addEventListener('ended',()=>{
   if(sounds[currentSoundIndex]===sound){
    if(currentSoundIndex<sounds.length-1)playSound(currentSoundIndex+1,true);
    else updateSoundboardUI();
   }
  });
 });
 if(currentSoundIndex<0&&sounds.length)currentSoundIndex=0;
 updateSoundboardUI();
 toast(`เพิ่มเพลง ${files.length} ไฟล์แล้ว`);
}
$('soundFiles').addEventListener('change',e=>{
 addSoundFiles(e.target.files);
 e.target.value='';
});
$('playlistAddFiles').addEventListener('click',()=>$('soundFiles').click());
$('openPlaylist').addEventListener('click',openPlaylist);
$('closePlaylist').addEventListener('click',closePlaylist);
$('playlistDone').addEventListener('click',closePlaylist);
$('playlistModal').addEventListener('click',e=>{
 if(e.target===$('playlistModal'))closePlaylist();
});
document.addEventListener('keydown',e=>{
 if(e.key==='Escape'&&!$('playlistModal').hidden)closePlaylist();
});
$('previousTrack').addEventListener('click',previousSound);
$('togglePlayback').addEventListener('click',toggleSoundPlayback);
$('nextTrack').addEventListener('click',nextSound);
updateSoundboardUI();
refreshPresets();restoreAutoSettings();initialiseSpeakerUI();
window.addEventListener('beforeunload',()=>{stopBrowser();sounds.forEach(s=>URL.revokeObjectURL(s.url));speakerRoutes.forEach(r=>{if(r){r.audio.pause();r.audio.srcObject=null;r.audio.remove()}});cancelAnimationFrame(raf)});
if(isFirefox){$('browserBtn').disabled=true;$('browserStatus').textContent='Firefox ไม่รองรับการจับเสียงแท็บผ่านเว็บแอป'}
else if(!navigator.mediaDevices?.getDisplayMedia){$('browserBtn').disabled=true;$('browserStatus').textContent='เบราว์เซอร์นี้ไม่รองรับ Tab Capture'}
updateBrowserButton();
})();