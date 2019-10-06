pub mod sdl  { use std::ffi::*;
               use std::os::raw::*;
               use std::sync::*;
               use std::*;
               use std::error::Error;
               use std::marker::*;
               use std::ptr::*;

               // Error Handling Types
               trait IsErr { fn is_err(&self)->bool; }
               #[derive(Debug)] #[repr(transparent)] struct ErrCheck<T:IsErr>(T);
               impl<T:IsErr> ErrCheck<T>
               {   fn unwrap(self)->Result<T,SdlError>
                   {   if self.0.is_err() { Err(SdlError::fetch()) }
                       else               { Ok(self.0)             } } }
               impl IsErr for c_int { fn is_err(&self)->bool { *self > 0 } }
               #[derive(Debug, Copy, Clone)]
               #[repr(transparent)]     struct WindowHandle(*const c_void);

               #[derive(Debug)]
               #[repr(transparent)] pub struct Window<'sdl>(WindowHandle,
                                                               PhantomData<&'sdl SDL>);

               impl<'sdl> IsErr for Window<'sdl> { fn is_err(&self)->bool {
                   (self.0).0.is_null() }}

               impl<'sdl> Drop for Window<'sdl> { fn drop(&mut self) {
                   unsafe { SDL_DestroyWindow(self.0); }}}

               impl<'sdl> Window<'sdl> { pub fn create_renderer(&self) -> Result<Renderer, Box<dyn Error>>
                                         { Ok(unsafe { SDL_CreateRenderer(self.0, -1, 0).unwrap()? }) } }
               #[repr(C)]
               union SdlEventUnion { event_type: u32,
                                     bytes: [u8;56],
                                     common: SdlCommonEvent,
                                     kbd: SdlKeyboardEvent, }
               #[repr(C)] #[derive(Debug,Copy,Clone)]
               pub struct SdlCommonEvent { pub event_type: u32,
                                           pub timestamp:  u32 }
               #[repr(C)] #[derive(Debug,Copy,Clone)]
               pub struct SdlKeyboardEvent { pub event_type: u32       ,
                                             pub timestamp : u32       ,
                                             pub windowID  : u32       ,
                                             pub state     : u8        ,
                                             pub repeat    : u8        ,
                                                 padding2  : u8        ,
                                                 padding3  : u8        ,
                                             pub sym       : SdlKeysym }
               #[repr(C)] #[derive(Debug,Copy,Clone)]
               pub struct SdlKeysym { pub scancode : c_int,
                                      pub keycode  : c_int,
                                      pub modifiers: u16  ,
                                          unused   : u32  }
               #[derive(Debug, Copy, Clone)] #[repr(transparent)]
               struct RendererHandle(*const c_void);

               #[derive(Debug)] #[repr(transparent)]
               pub struct Renderer<'win>(RendererHandle,
                                         PhantomData<&'win Window<'win>>);

               impl<'win> IsErr for Renderer<'win> { fn is_err(&self)->bool {
                   (self.0).0.is_null() }}

               impl<'win> Drop for Renderer<'win> { fn drop(&mut self) {
                   unsafe { SDL_DestroyRenderer(self.0); }}}

               impl<'win> Renderer<'win> { pub fn start_frame<'r>(&'r self, clear_color: (u8,u8,u8))
                                           -> Result<Canvas<'r,'win>, Box<dyn Error>>
                                           {   unsafe { SDL_SetRenderDrawColor(self.0,
                                                                               clear_color.0,
                                                                               clear_color.1,
                                                                               clear_color.2,
                                                                               255           ).unwrap()?;
                                                        SDL_RenderClear       (self.0        ).unwrap()?; }
                                               Ok(Canvas(self)) }
                                           pub fn load_texture<'r>(&'r self, s: &Surface<'r>)
                                           ->Result<Texture<'r>, Box<dyn Error>>
                                           { Ok( unsafe { SDL_CreateTextureFromSurface(self.0, s.0)
                                                          .unwrap()?                                })} }
               #[derive(Debug, Copy, Clone)] #[repr(C)]
               pub struct Rect { pub x: c_int, pub y: c_int,
                                 pub w: c_int, pub h: c_int }
               #[repr(transparent)] #[derive(Debug,Copy,Clone)]
               struct RWopsHandle(*mut RWopsHeader);

               #[repr(transparent)] #[derive(Debug)]
               pub struct RWops<'sdl>(RWopsHandle, PhantomData<&'sdl SDL>);
               //impl<'sdl> Drop for RWops<'sdl> { fn drop(&mut self) { unsafe {
               //    let handle:RWopsHandle = self.0;
               //    if !handle.0.is_null()
               //    { ((*(handle.0)).close)(handle); }}}}
               impl<'sdl> IsErr for RWops<'sdl> { fn is_err(&self)->bool {
                   (self.0).0.is_null() }}

               #[repr(C)]
               struct RWopsHeader {
                   size: extern fn (RWopsHandle)->i64,
                   seek: extern fn (RWopsHandle, i64, c_int)->i64,
                   read: extern fn (RWopsHandle, *mut c_void, isize, isize)->isize,
                   write: extern fn (RWopsHandle, *const c_void, isize, isize)->isize,
                   close: extern fn (RWopsHandle)->c_int
               }
               #[repr(transparent)] #[derive(Debug,Copy,Clone)]
               pub struct SurfaceHandle(*const c_void);
               #[repr(transparent)] #[derive(Debug)]
               pub struct Surface<'sdl>(SurfaceHandle, PhantomData<&'sdl SDL>);
               impl<'sdl> Drop for Surface<'sdl> { fn drop(&mut self) { unsafe {
                   SDL_FreeSurface(self.0); }}}
               impl<'sdl> IsErr for Surface<'sdl> { fn is_err(&self)->bool {
                   (self.0).0.is_null() }}
               #[repr(transparent)] #[derive(Debug,Copy,Clone)]
               pub struct TextureHandle(*const c_void);
               #[repr(transparent)] #[derive(Debug)]
               pub struct Texture<'r>(TextureHandle, PhantomData<&'r Renderer<'r>>);
               impl<'r> Drop for Texture<'r> { fn drop(&mut self) { unsafe {
                   SDL_DestroyTexture(self.0); }}}
               impl<'sdl> IsErr for Texture<'sdl> { fn is_err(&self)->bool {
                   (self.0).0.is_null() }}
               #[link(name="SDL2")] extern { fn SDL_GetError() -> *const c_char;
                                             // Initialization and cleanup
                                             fn SDL_SetMainReady();
                                             fn SDL_Init(flags: u32)->ErrCheck<c_int>;
                                             fn SDL_Quit();
                                             fn SDL_CreateWindow<'sdl>
                                             ( title: *const c_char,
                                               x: c_int, y: c_int,
                                               w: c_int, h: c_int,
                                               flags: u32
                                             ) -> ErrCheck<Window<'sdl>>;

                                             fn SDL_DestroyWindow(win: WindowHandle);
                                             fn SDL_PumpEvents();
                                             fn SDL_PollEvent(ev:*mut SdlEventUnion)->c_int;
                                             fn SDL_Delay(ms:u32);   fn SDL_GetTicks()->u32;
                                             fn SDL_CreateRenderer<'win>
                                             (    win: WindowHandle,
                                                index: c_int,
                                                flags: u32            ) -> ErrCheck<Renderer<'win>>;
                                             fn SDL_DestroyRenderer
                                             ( handle: RendererHandle ) -> ();
                                             fn SDL_SetRenderDrawColor
                                             (   handle: RendererHandle,
                                                 r:u8, g:u8, b:u8, a:u8  ) -> ErrCheck<c_int>;
                                             fn SDL_RenderClear
                                             (   handle: RendererHandle  ) -> ErrCheck<c_int>;
                                             fn SDL_RenderPresent( handle: RendererHandle  );
                                             fn SDL_RenderFillRects(r    : RendererHandle,
                                                                    rects: *const Rect,
                                                                    count: c_int           )->ErrCheck<c_int>;
                                             fn SDL_RWFromConstMem<'a>(mem : *const u8,
                                                                       size: c_int     )->ErrCheck<RWops<'a>>;
                                             fn SDL_FreeSurface(h:SurfaceHandle);
                                             fn SDL_CreateTextureFromSurface<'r>
                                             ( r:RendererHandle, s:SurfaceHandle ) -> ErrCheck<Texture<'r>>;
                                             fn SDL_DestroyTexture(tex: TextureHandle);
                                             fn SDL_QueryTexture(tex:    TextureHandle,
                                                                 format: *mut u32,
                                                                 access: *mut c_int,
                                                                 w:      *mut c_int,
                                                                 h:      *mut c_int) -> ErrCheck<c_int>;
                                             fn SDL_RenderCopy(r:   RendererHandle,
                                                               t:   TextureHandle,
                                                               src: *const Rect,
                                                               dst: *const Rect    ) -> ErrCheck<c_int>; }
               #[derive(Debug, Clone)] pub struct SdlError( String );
               impl SdlError
               {   fn fetch()->SdlError
                   {   SdlError( unsafe { CStr::from_ptr(SDL_GetError())
                                          .to_string_lossy()
                                          .into_owned()                 } ) } }

               impl Error for SdlError {}

               impl fmt::Display for SdlError
               {   fn fmt(&self, f: &mut fmt::Formatter<'_>)
                   -> fmt::Result { write!(f, "{:?}", self) } }
               #[derive(Debug)] pub struct SDL { guard: MutexGuard<'static, ()> }
               impl SDL { pub fn init()->Result<SDL, Box<dyn Error>>
                          {   let guard = unsafe
                                          {   static mut MUTEX        : Option<Mutex<()>> = None;
                                              static     MUTEX_EXISTS : Once              = Once::new();

                                              MUTEX_EXISTS.call_once(|| { MUTEX = Some(Mutex::new(())); });
                                              MUTEX.as_ref().unwrap()
                                          }.try_lock()?;
                              let flags = 0x20; //SDL_VIDEO
                              unsafe { SDL_SetMainReady();
                                       SDL_Init(flags).unwrap()?; }
                              Ok(SDL { guard })
                          }
                          pub fn create_win<'sdl>(&'sdl self, title:&str, pos:(i32,i32), size:(i32,i32))
                          -> Result<Window<'sdl>, Box<dyn Error>> { unsafe {
                              let c_title = CString::new(title)?;
                              Ok(SDL_CreateWindow(c_title.as_ptr(),
                                                  pos.0,  pos.1,
                                                  size.0, size.1,
                                                  0                 ).unwrap()?) }}
                          pub fn iter_events<'a>(&'a self) -> SdlPendingEventsIter<'a>
                          {   unsafe { SDL_PumpEvents() };
                              SdlPendingEventsIter { _sdl: self } }
                          pub fn delay(&self, ms:u32) { unsafe { SDL_Delay(ms); }; }
                          pub fn ticks(&self) -> u32  { unsafe { SDL_GetTicks() } }
                          pub fn load_bytes<'sdl>(&'sdl self, bytes: &'static [u8])
                          ->Result<RWops<'sdl>, Box<dyn Error>>
                          { Ok( unsafe{ SDL_RWFromConstMem(bytes.as_ptr(),
                                                           bytes.len() as c_int).unwrap()? } ) }
                          pub fn load_png<'sdl>(&'sdl self, bytes: &'static [u8])
                          ->Result<Surface<'sdl>, Box<dyn Error>>
                          { Ok( unsafe { IMG_LoadPNG_RW(self.load_bytes(bytes)?.0)
                                         .unwrap()?                                })}
                          pub fn load_font<'sdl>(&'sdl self, size: c_int, bytes: &'static [u8])
                          ->Result<Font<'sdl>, Box<dyn Error>>
                          {   static SDLTTF_INIT:Once = Once::new();
                              SDLTTF_INIT.call_once(|| { unsafe { TTF_Init(); } });
                              Ok(unsafe { TTF_OpenFontRW( self.load_bytes(bytes)?.0,
                                                          0, size                   )})} }
               impl Drop for SDL
               { fn drop(&mut self) { unsafe { SDL_Quit(); } } }
               #[derive(Debug, Copy, Clone)]
               pub enum SdlEvent { Other(SdlCommonEvent),
                                   Quit(SdlCommonEvent),
                                   KeyUp(i32, SdlKeyboardEvent), KeyDn(i32, SdlKeyboardEvent) }
               impl From<SdlEventUnion> for SdlEvent
               {   fn from(raw: SdlEventUnion) -> SdlEvent { unsafe 
                   {   match raw.event_type { 0x100 => SdlEvent::Quit(raw.common),
                                              0x301 => SdlEvent::KeyUp(raw.kbd.sym.scancode, raw.kbd),
                                              0x300 => SdlEvent::KeyDn(raw.kbd.sym.scancode, raw.kbd),
                                              _ => SdlEvent::Other(raw.common) }
                   }}
               }
               pub struct SdlPendingEventsIter<'a> { _sdl: &'a SDL }
               impl<'a> Iterator for SdlPendingEventsIter<'a>
               {   type Item = SdlEvent;
                   fn next(&mut self) -> Option<SdlEvent>
                   {   let mut result = SdlEventUnion { event_type: 0 };
                       let code = unsafe
                       { SDL_PollEvent(&mut result as *mut SdlEventUnion) };
                       if code > 0 { Some(SdlEvent::from(result)) }
                       else        { None                         } } }
               pub struct Canvas<'r, 'w:'r>(&'r Renderer<'w>);
               impl<'r,'w:'r> Drop for Canvas<'r,'w> { fn drop(&mut self) {
                   unsafe { SDL_RenderPresent((self.0).0) };
               }}
               impl<'r,'w:'r> Canvas<'r,'w> { pub fn set_color(&self, r:u8, g:u8, b:u8, a:u8)
                                              -> Result<(), Box<dyn Error>>
                                              { Ok( unsafe { SDL_SetRenderDrawColor((self.0).0, r, g, b, a)
                                                             .unwrap()?;                                    
                                                           })}
                                              pub fn fill_rects(&self, rects: &Vec<Rect>)
                                              -> Result<(), Box<dyn Error>>
                                              { Ok( unsafe { SDL_RenderFillRects((self.0).0,
                                                                                 rects.as_ptr(),
                                                                                 rects.len() as i32).unwrap()?; })}
                                              pub fn blit(&self, tex:&Texture, dest:&Rect)
                                              -> Result<(), Box<dyn Error>>
                                              { Ok( unsafe { SDL_RenderCopy((self.0).0,
                                                                            tex.0,
                                                                            null(),
                                                                           dest as *const _).unwrap()?; })}
                                              pub fn blit_center(&self, tex:&Texture, pos:(i32,i32))
                                              -> Result<(), Box<dyn Error>>
                                              { let (w,h) = tex.get_size()?;
                                                let dest = Rect { x: pos.0 - w/2, y: pos.1 - h/2, w, h };
                                                Ok(self.blit(tex, &dest)?)                                } }
               #[link(name="SDL2_image")] extern
               {   fn IMG_LoadPNG_RW<'a>(h:RWopsHandle)->ErrCheck<Surface<'a>>; }
               impl<'r> Texture<'r> {
                   pub fn get_size(&self) -> Result<(c_int, c_int), Box<dyn Error>>
                   {   let mut w:c_int = 0;
                       let mut h:c_int = 0;
                       unsafe { SDL_QueryTexture(self.0,
                                                 null_mut(),
                                                 null_mut(),
                                                 &mut w as *mut _,
                                                 &mut h as *mut _) }.unwrap()?;
                       Ok((w,h)) }}
               #[link(name="SDL2_ttf")] extern {
                   fn TTF_Init()->c_int;
                   fn TTF_OpenFontRW<'sdl>(src   : RWopsHandle,
                                           free  : c_int,
                                           ptsize: c_int        )->Font<'sdl>;
                   fn TTF_CloseFont(f: FontHandle);
                   fn TTF_SetFontStyle(f: FontHandle, style:c_int);
                   fn TTF_RenderUTF8_Blended<'sdl>(f   : FontHandle,
                                                   text: *const c_char,
                                                   fg  : Color         )
                                                      ->Surface<'sdl>;
               }

               #[repr(C)] #[derive(Debug,Copy,Clone)]
               pub struct Color { pub r: u8, pub g: u8, pub b:u8, pub  a:u8 }
               #[repr(transparent)] #[derive(Debug,Copy,Clone)]
               struct FontHandle(*const c_void);
               #[repr(transparent)] #[derive(Debug)]
               pub struct Font<'sdl>(FontHandle, PhantomData<&'sdl SDL>);
               impl<'sdl> Drop for Font<'sdl> { fn drop(&mut self) { unsafe {
                   TTF_CloseFont(self.0); }}}
               impl<'sdl> Font<'sdl> {
                   pub fn bold(self)->Self { unsafe { TTF_SetFontStyle(self.0,1);}; self}
                   pub fn render(&self, text: &str, color: Color)
                   ->Result<Surface<'sdl>, Box<dyn Error>> {
                       let c_text = CString::new(text)?;
                       let surf = unsafe { TTF_RenderUTF8_Blended(self.0,
                                                                c_text.as_ptr(),
                                                                 color) };
                       assert!(!(surf.0).0.is_null());
                       Ok(surf)     }}
 }  // SDL Bindings
pub mod fut  { use std::cell::*;
               use std::rc::Rc;
               use std::pin::*;
               use std::task::*;
               use std::future::Future;
               use std::fmt::Debug;

               type PendingTaskInner =
                   RefCell<Option<Pin<Box<dyn Future<Output = ()> + 'static>>>>;

               #[derive(Clone)]
               pub struct PendingTask(Rc<PendingTaskInner>);
               impl PendingTask { unsafe fn from_ptr(p: *const ())->PendingTask {
                                      PendingTask(Rc::from_raw(p as *const PendingTaskInner))
                                  }
                                  fn clone_as_ptr(&self)->*const () {
                                      Rc::into_raw(Rc::clone(&self.0)) as *const ()
                                  } }
               fn task_queue() -> RefMut<'static, Vec<PendingTask>> {
                   static mut QUEUE: Option<RefCell<Vec<PendingTask>>> = None;
                   static INIT: std::sync::Once = std::sync::Once::new();
                   INIT.call_once(|| { unsafe { QUEUE = Some(RefCell::new(vec![])); }});
                   unsafe { QUEUE.as_ref().unwrap().borrow_mut() }
               }
               pub fn enqueue(f: impl Future<Output = ()> + 'static)->PendingTask
               {   let result = PendingTask(
                                   Rc::new( RefCell::new( Some( Box::pin(f)))) );
                   task_queue().push( result.clone() );
                   result                                                       }
               pub fn run_tasks() { while run_one_task() {} }
               fn run_one_task()->bool
               {   let task = task_queue().pop();
                   match task { None    =>   false,
                                Some(t) => { let w = unsafe { Waker::from_raw( RawWaker::new(t.clone_as_ptr(),
                                                                                             &VTABLE         ) )};
                                             let mut optfut = t.0.borrow_mut();
                                             if optfut.is_some()
                                             {   let result = optfut.as_mut().unwrap()
                                                              .as_mut().poll(&mut Context::from_waker(&w));
                                                 if result.is_ready() { *optfut = None; }                    };
                                             true                     }}}
               static VTABLE:RawWakerVTable = RawWakerVTable::new(
                   raw_clone, raw_wake, raw_wake_by_ref, raw_drop
               );
               unsafe fn raw_clone(p: *const ()) -> RawWaker {
                   let t = PendingTask::from_ptr(p);
                   let result = RawWaker::new(t.clone_as_ptr(), &VTABLE);
                   assert_eq!(Rc::into_raw(t.0) as *const (), p);
                   result
               }
               unsafe fn raw_wake(p: *const ()) {
                   let t = PendingTask::from_ptr(p);
                   task_queue().push(t);
               }
               unsafe fn raw_wake_by_ref(p: *const ()) {
                   let t = PendingTask::from_ptr(p);
                   task_queue().push(t.clone());
                   assert_eq!(Rc::into_raw(t.0) as *const (), p);
               }
               unsafe fn raw_drop(p: *const ()) {
                   let _t = PendingTask::from_ptr(p);
               }
               use std::sync::{Arc,Mutex};
               #[derive(Debug)]
               pub struct NotificationPool<T:Clone+Debug>(Mutex<NotifPoolData<T>>);
               #[derive(Debug)]
               struct NotifPoolData<T> { result: Option<T>,
                                         wakers: Vec<Option<Waker>> }
               impl<T:Clone+Debug> NotificationPool<T>
               { pub fn new()->Arc<Self> {
                     Arc::new(
                         NotificationPool(
                             Mutex::new( NotifPoolData{ result:None,
                                                        wakers:vec![] })))}
                 pub fn notify(&self, result:T) {
                     let wakers =
                     {   let mut self_mut = self.0.lock().unwrap();
                         assert!(self_mut.result.is_none());
                         self_mut.result = Some(result);
                         std::mem::replace(&mut self_mut.wakers, vec![]) };
                     for maybe_w in wakers.into_iter()
                     {   if let Some(waker) = maybe_w { waker.wake(); }}     }
                 pub fn wait(self: Arc<Self>)->NotificationFuture<T> {
                     let id: usize =
                     {   let mut self_mut = self.0.lock().unwrap();
                         self_mut.wakers.push(None);
                         self_mut.wakers.len() - 1                  };
                     NotificationFuture { id, pool: self }               } }
               #[derive(Debug)]
               pub struct NotificationFuture<T:Clone+Debug>
               { pool: Arc<NotificationPool<T>>,
                 id  : usize                   }
               impl<T:Clone+Debug> Future for NotificationFuture<T>
               {   type Output = T;
                   fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<T>
                   {   let mut pool = self.pool.0.lock().unwrap();
                       if let Some(ref result) = pool.result
                       {   Poll::Ready(result.clone()) }
                       else {  pool.wakers[self.id] = Some( cx.waker()
                                                              .clone() );
                               Poll::Pending                               } } }
               impl<T:Clone+Debug> Drop for NotificationFuture<T>
               { fn drop(&mut self)
                 { let _w: Option<Waker> // Dont't drop while holding lock
                       = { let mut pool = self.pool.0.lock().unwrap();
                           if pool.wakers.len() > self.id
                           { std::mem::replace(&mut pool.wakers[self.id],
                                               None                     )}
                           else { None }                                   };}}
               impl<T:Clone+Debug> Clone for NotificationFuture<T>
               {   fn clone(&self)->NotificationFuture<T>
                   {   Arc::clone(&self.pool).wait()    }  }
               #[derive(Clone,Debug)]
               struct StreamArg<T:Clone+Debug+'static>( T,
                                               NotificationFuture<StreamArg<T>>);
               pub struct StreamSource<T:Clone+Debug+'static>
               {    pool: Arc<NotificationPool<StreamArg<T>>>  }
               impl<T:Clone+Debug> StreamSource<T> { pub fn new() -> StreamSource<T>
                                                     {   StreamSource { pool: NotificationPool::new() } }
                                                     pub fn send(&mut self, msg:T)
                                                     {   let next_pool = NotificationPool::<StreamArg<T>>::new();
                                                         let payload = StreamArg( msg, Arc::clone(&next_pool).wait());
                                                         self.pool.notify(payload);
                                                         self.pool = next_pool;                                       }
                                                     pub fn watch(&self) -> StreamReader<T>
                                                     {   StreamReader { fut: Arc::clone(&self.pool).wait() } } }
               #[derive(Clone, Debug)]
               pub struct StreamReader<T:Clone+Debug+'static>
               {   fut: NotificationFuture<StreamArg<T>>   }

               impl<T:Clone+Debug+'static> StreamReader<T>
               { pub async fn next(&mut self) -> T
                 {   let StreamArg(result, new_fut) = self.fut.clone().await;
                     self.fut = new_fut;
                     return result;                                          }
                 pub fn filter(self, f: impl Fn(&T)->bool + 'static) -> StreamReader<T>
                 {   let mut source = self;
                     let mut newsource = StreamSource::<T>::new();
                     let result = newsource.watch();
                     enqueue(async move
                     {   loop {  let val:T = source.next().await;
                                 if f(&val) { newsource.send(val);   }}});
                     result                                                  }
                 pub fn map<R>(self, f: impl Fn(T)->R + 'static) -> StreamReader<R>
                 where R: Debug+Clone+'static
                 {   let mut source = self;
                     let mut newsource = StreamSource::<R>::new();
                     let result = newsource.watch();
                     enqueue(async move
                     {   loop {  let val:T = source.next().await;
                                 newsource.send(f(val));             }});
                     result                                                  }
                 pub fn filtermap<R>(self, f: impl Fn(T)->Option<R> + 'static) -> StreamReader<R>
                 where R: Debug+Clone+'static
                 {   let mut source = self;
                     let mut newsource = StreamSource::<R>::new();
                     let result = newsource.watch();
                     enqueue(async move
                     {   loop {  let val:T = source.next().await;
                                 if let Some(r) = f(val) { newsource.send(r) }}});
                     result                                                  } } }  // Async, Futures
pub mod sim  { #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
               pub enum Command { FrameAdvance( u32 ),
                                  Step( i32, i32 ), }
               use crate::fut::*;
               use std::cell::RefCell;

               #[derive(Debug, Default)]
               pub struct GameState { pub terrain:Vec<Vec<Terrain>>,
                                      pub player:Player,
                                      pub camera:(f32, f32),
                                      pub floor_marks:Vec<(f32,f32,&'static str)>,
                                      pub enemies:Vec<(usize, usize)>,
                                      pub wrecks:Vec<(usize, usize)>, }
               impl GameState
               { pub fn current() -> &'static RefCell<GameState>
                 { static mut STATE: Option<RefCell<GameState>> = None;
                   static INIT: std::sync::Once = std::sync::Once::new();
                   INIT.call_once(
                           || { unsafe
                                { STATE = Some(RefCell::new(
                                                   Default::default())); } } );
                   unsafe { STATE.as_ref().unwrap() }                          }}
               macro_rules! select
               { ($s:ident : $p:pat => $e:expr) => { select!(($s): $p => $e) };
                 (($stream:expr): $pat:pat => $expr:expr) =>
                 { ($stream).clone().filtermap(|value|
                   { if let $pat = value { Some($expr) } else { None } }) }; }
               pub async fn start(firehose: StreamReader<Command>) {
                   use Command::*;
                   {   let mut gs = GameState::current().borrow_mut();
                       for y in 0..40
                       {   gs.terrain.push(vec![]);
                           for x in 0..40
                           {   gs.terrain[y].push( match (x^y)&1
                                                       { 0 => Terrain::Floor,
                                                         _ => Terrain::Empty } ); } }
                       gs.player.loc = (20,20);
                       gs.camera = (15.,15.);
                       for mark in [ (18.,18.,"q"), (20.,16.,"w"),
                                     (22.,18.,"e"), (18.,22.,"a"),
                                     (20.,24.,"s"), (22.,22.,"d") ].into_iter()
                           { gs.floor_marks.push(*mark); }
                       gs.enemies = vec![(25,9), (3,3)];
                   }

                   use std::sync::atomic::*;
                   use std::sync::atomic::Ordering::*;
                   static T_PREV:AtomicU32 = AtomicU32::new(0);
                   let timing = select!( firehose: FrameAdvance(t)
                                         => (t, t-T_PREV.swap(t, Relaxed)) );
                   let steps = select!(firehose: Step(x, y) => (x, y));
                   enqueue(stepper(steps));
                   enqueue(camera_track(timing.clone()));
               }
               #[derive(Debug,Eq,PartialEq)]
               pub enum Terrain { Empty, Floor }
               #[derive(Debug,Default)]
               pub struct Player { pub loc: (usize, usize) }
               async fn stepper(mut steps: StreamReader<(i32,i32)>) { loop
               {   let (dx, dy) = steps.next().await;
                   let mut gs = GameState::current().borrow_mut();
                   let (x,y) = (gs.player.loc.0 as i32 + dx,
                                gs.player.loc.1 as i32 + dy);
                   if x < 0 || y < 0 { continue }
                   let loc:(usize, usize) = (x as usize, y as usize);
                   if loc.1 >= gs.terrain.len()        { continue };
                   if loc.0 >= gs.terrain[loc.1].len() { continue };
                   if gs.wrecks.contains(&loc)         { continue };
                   match gs.terrain[loc.1][loc.0]
                   {   Terrain::Floor => { gs.player.loc = loc; }
                       Terrain::Empty => { continue }             };
                   for i in 0..gs.enemies.len() {let dx = gs.player.loc.0 as i32 - gs.enemies[i].0 as i32;
                                                 let dy = gs.player.loc.1 as i32 - gs.enemies[i].1 as i32;
                                                 let mut e = &mut gs.enemies[i];
                                                      if dx == 0 &&               dy >  0 {           e.1 += 2; }
                                                 else if dx <  0 && -3*dx < dy && dy >  0 {           e.1 += 2; }
                                                 else if dx >  0 &&  3*dx < dy && dy >  0 {           e.1 += 2; }
                                                 else if dx == 0 &&               dy <  0 {           e.1 -= 2; }
                                                 else if dx <  0 &&  3*dx > dy && dy <  0 {           e.1 -= 2; }
                                                 else if dx >  0 && -3*dx > dy && dy <  0 {           e.1 -= 2; }
                                                 else if dx >  0 &&                dy > 0 { e.0 += 1; e.1 += 1; }
                                                 else if dx >  0 &&                dy < 0 { e.0 += 1; e.1 -= 1; }
                                                 else if dx <  0 &&                dy < 0 { e.0 -= 1; e.1 -= 1; }
                                                 else if dx <  0 &&                dy > 0 { e.0 -= 1; e.1 += 1; }
}

                   let mut deadlist:Vec<usize> = vec![];
                   for i in 0..gs.enemies.len()
                   {   let mut dead:bool = false;
                       { let loc = gs.enemies[i];
                              if gs.player.loc == loc { return; } // Game Over
                         else if gs.wrecks.contains(&loc) { dead = true; }
                         else {
                             for j in 0..gs.enemies.len() {
                                 if j != i && gs.enemies[j] == loc {
                                     dead = true; gs.wrecks.push(loc);
                         }}} }
                       if dead { deadlist.push(i) };
                   }
                   while !deadlist.is_empty()
                   { let id = deadlist.pop().unwrap();
                     println!("kill {:?}", id);
                     gs.enemies.remove(id); }
                   if gs.enemies.len() < 2 {
                       use std::sync::atomic::*;
                       static NUM_ENEMIES:AtomicUsize = AtomicUsize::new(3);
                       for n in 0..NUM_ENEMIES.fetch_add(1, Ordering::Relaxed) {
                           loop {
                               let coord = random_coord();
                               if gs.wrecks.contains(&coord) {continue};
                               if gs.enemies.contains(&coord) {continue};
                               if (gs.player.loc.0 as i32 - coord.0 as i32).abs()
                                + (gs.player.loc.1 as i32 - coord.1 as i32).abs()
                                < 5 { continue };
                               gs.enemies.push(coord);
                               break;
                           }
                       }
                   }
               }}
               async fn camera_track(mut times: StreamReader<(u32,u32)>) { loop
               {   let (_t, dt) = times.next().await;
                   let mut gs = GameState::current().borrow_mut();
                   let coeff: f32 = 0.9999f32.powi(dt as i32);
                   gs.camera.0 = gs.player.loc.0 as f32 
                               + coeff * (gs.camera.0 - gs.player.loc.0 as f32);
                   gs.camera.1 = gs.player.loc.1 as f32 
                               + coeff * (gs.camera.1 - gs.player.loc.1 as f32); }}
               static COORDS:[(usize,usize);200] = [(17, 35), (6, 22), (13, 31),
               (28, 2), (15, 29), (34, 26), (3, 9), (14, 12), (32, 34), (5, 31),
               (25, 37), (22, 28), (17, 31), (0, 22), (6, 32), (9, 1), (11, 39),
               (36, 32), (1, 33), (33, 1), (5, 15), (32, 10), (36, 26), (15, 1),
               (16, 12), (14, 28), (38, 38), (21, 25), (31, 11), (9, 23),
               (0, 38), (22, 4), (36, 38), (13, 1), (34, 6), (22, 34), (24, 30),
               (34, 2), (21, 19), (34, 34), (17, 11), (23, 23), (39, 29),
               (13, 39), (23, 37), (25, 3), (27, 13), (34, 30), (0, 0), (5, 9),
               (38, 18), (28, 6), (20, 14), (35, 37), (34, 30), (30, 8),
               (16, 30), (34, 36), (25, 1), (19, 27), (32, 14), (24, 14),
               (14, 6), (34, 20), (25, 23), (6, 30), (30, 34), (27, 27),
               (17, 17), (16, 38), (5, 33), (4, 16), (8, 6), (38, 2), (34, 16),
               (8, 14), (13, 39), (19, 21), (35, 21), (33, 15), (38, 4),
               (22, 8), (36, 16), (18, 22), (1, 9), (16, 12), (11, 5), (23, 29),
               (3, 37), (22, 34), (17, 37), (18, 8), (35, 19), (0, 34),
               (39, 35), (27, 17), (31, 27), (36, 28), (26, 6), (30, 22),
               (23, 19), (39, 11), (10, 24), (16, 14), (1, 35), (3, 37),
               (10, 2), (5, 3), (6, 6), (28, 6), (31, 9), (24, 18), (33, 31),
               (11, 13), (11, 17), (4, 36), (31, 13), (7, 37), (28, 10),
               (34, 26), (3, 17), (12, 20), (33, 35), (27, 33), (9, 27),
               (17, 11), (4, 20), (38, 32), (36, 4), (9, 3), (28, 38), (13, 35),
               (28, 2), (25, 33), (12, 18), (16, 6), (37, 15), (7, 21),
               (19, 15), (18, 8), (2, 8), (23, 1), (25, 9), (12, 8), (13, 39),
               (21, 17), (23, 11), (35, 1), (1, 7), (1, 7), (5, 15), (1, 1),
               (10, 14), (27, 13), (39, 17), (9, 33), (37, 19), (34, 32),
               (12, 6), (32, 4), (23, 29), (13, 29), (37, 27), (2, 38), (9, 21),
               (12, 38), (8, 6), (27, 7), (22, 2), (26, 32), (36, 28), (5, 27),
               (36, 26), (22, 28), (20, 14), (17, 21), (29, 39), (15, 29),
               (39, 21), (1, 13), (14, 16), (13, 9), (1, 37), (29, 23), (21, 1),
               (35, 29), (18, 32), (37, 39), (24, 36), (7, 5), (12, 26),
               (14, 26), (39, 29), (2, 4), (39, 31), (9, 39), (13, 5), (20, 38),
               (33, 37), (9, 17)];
               use std::sync::atomic::*;
               static NEXT_COORD:AtomicUsize = AtomicUsize::new(0);
               fn random_coord() -> (usize, usize) {
                   let coord = NEXT_COORD.fetch_add(1, Ordering::Relaxed);
                   return COORDS[coord % COORDS.len()];
               } }  // Game Logic
pub mod main { use std::error::*;
               use crate::sdl::*;
               use crate::fut::*;
               use crate::sim;
               use crate::sim::Command::*;

               pub fn run()->Result<(), Box<dyn Error>>
               {   let sdl = SDL::init()?;
                   let win = sdl.create_win("LD45— Start With Nothing",
                                            (0, 0), (800, 600))?;
                   let renderer = win.create_renderer()?;
                   macro_rules!
                   PNG { ( $file:tt) => { renderer.load_texture(
                                               &sdl.load_png(include_bytes!(
                                                                       $file))?)? }};
                   let font = sdl.load_font(36, include_bytes!("Go-Mono.ttf"))?;
                   let boldfont = sdl.load_font(36, include_bytes!("Go-Mono.ttf"))?.bold();
                   macro_rules!
                   DRAW_TEXT { ( $str:expr, $color:expr) =>
                           { renderer.load_texture(
                                       &font.render($str, { let (r,g,b,a)=$color;
                                                            Color { r,g,b,a }  })?)?}};
                   macro_rules!
                   DRAW_BOLD { ( $str:expr, $color:expr) =>
                           { renderer.load_texture(
                                       &boldfont.render($str, { let (r,g,b,a)=$color;
                                                            Color { r,g,b,a }  })?)?}};

                   let mut command_queue = StreamSource::<sim::Command>::new();
                   let command_stream = command_queue.watch();
                   enqueue(sim::start(command_stream));
                   let tex_floor = PNG!("flathex.png");
                   let tex_player    = DRAW_TEXT!("@", (88,100,232,255));
                   let tex_player_bg = DRAW_BOLD!("@", (22,25,60,255));
                   let tex_enemy    = DRAW_TEXT!("X", (232,100,88,255));
                   let tex_enemy_bg = DRAW_BOLD!("X", (60,25,22,255));
                   let tex_wreck = DRAW_BOLD!("#", (44,44,44,255));
                   'mainloop: loop
                   {   sdl.delay(10);
                       for e in sdl.iter_events() {
                           match e { SdlEvent::Quit(_) => { break 'mainloop; }
                                     SdlEvent::KeyDn(0x014, _) => { command_queue.send(Step(-1,-1)); }
                                     SdlEvent::KeyDn(0x01a, _) => { command_queue.send(Step( 0,-2)); }
                                     SdlEvent::KeyDn(0x008, _) => { command_queue.send(Step( 1,-1)); }
                                     SdlEvent::KeyDn(0x004, _) => { command_queue.send(Step(-1, 1)); }
                                     SdlEvent::KeyDn(0x016, _) => { command_queue.send(Step( 0, 2)); }
                                     SdlEvent::KeyDn(0x007, _) => { command_queue.send(Step( 1, 1)); }
                                     SdlEvent::KeyUp(_,_) => {}
                                     SdlEvent::KeyDn(_,_) => {}
                                     event@_ => { println!("Unhandled event: {:?}",
                                                           event);                  } } }
                       command_queue.send(sim::Command::FrameAdvance(sdl.ticks()));
                       run_tasks();
                       { let game_state = sim::GameState::current().borrow();
                         let canvas = renderer.start_frame((128,0,255))?;
                         { for y in 0..game_state.terrain.len()
                           { for x in 0..game_state.terrain[y].len()
                             { if game_state.terrain[y][x] == sim::Terrain::Floor
                               { let center = igrid_to_px((x, y), game_state.camera);
                                 canvas.blit_center(&tex_floor, center)?;            } } } }
                         { for (x,y,s) in game_state.floor_marks.iter() {
                               canvas.blit_center(&DRAW_TEXT!(s,(88,88,111,55)),
                                                  grid_to_px((*x,*y), game_state.camera))?;} }
                         { let loc = igrid_to_px(game_state.player.loc, game_state.camera);
                           canvas.blit_center(&tex_player_bg, loc)?;
                           canvas.blit_center(&tex_player,    loc)?;
                           for world_loc in game_state.enemies.iter()
                           {   let loc = igrid_to_px(*world_loc, game_state.camera);
                               canvas.blit_center(&tex_enemy_bg, loc)?;
                               canvas.blit_center(&tex_enemy,    loc)?;                }
                           for world_loc in game_state.wrecks.iter()
                           {   let loc = igrid_to_px(*world_loc, game_state.camera);
                               canvas.blit_center(&tex_wreck,    loc)?;                } }
                       }
                   }
                   Ok(())
               }
               fn grid_to_px(obj:(f32, f32), cam:(f32, f32))->(i32,i32)
               { (((obj.0-cam.0)*36.).floor() as i32+400,
                  ((obj.1-cam.1)*21.).floor() as i32+300) }
               fn igrid_to_px(obj:(usize, usize), cam:(f32, f32))->(i32,i32)
               { grid_to_px((obj.0 as f32, obj.1 as f32), cam) } }
