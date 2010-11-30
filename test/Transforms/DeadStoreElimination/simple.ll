; RUN: opt < %s -basicaa -dse -S | FileCheck %s
target datalayout = "E-p:64:64:64-a0:0:8-f32:32:32-f64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-v64:64:64-v128:128:128"

define void @test1(i32* %Q, i32* %P) {
        %DEAD = load i32* %Q
        store i32 %DEAD, i32* %P
        store i32 0, i32* %P
        ret void
; CHECK: @test1
; CHECK-NEXT: store i32 0, i32* %P
; CHECK-NEXT: ret void
}

; PR8576 - Should delete store of 10 even though p/q are may aliases.
define void @test2(i32 *%p, i32 *%q) {
  store i32 10, i32* %p, align 4
  store i32 20, i32* %q, align 4
  store i32 30, i32* %p, align 4
  ret void
; CHECK: @test2
; CHECK-NEXT: store i32 20
}


; PR8677
@g = global i32 1

define i32 @test3(i32* %g_addr) nounwind {
; CHECK: @test3
; CHECK: load i32* %g_addr
  %g_value = load i32* %g_addr, align 4
  store i32 -1, i32* @g, align 4
  store i32 %g_value, i32* %g_addr, align 4
  %tmp3 = load i32* @g, align 4
  ret i32 %tmp3
}


define void @test4(i32* %Q) {
        %a = load i32* %Q
        volatile store i32 %a, i32* %Q
        ret void
; CHECK: @test4
; CHECK-NEXT: load i32
; CHECK-NEXT: volatile store
; CHECK-NEXT: ret void
}

define void @test5(i32* %Q) {
        %a = volatile load i32* %Q
        store i32 %a, i32* %Q
        ret void
; CHECK: @test5
; CHECK-NEXT: volatile load
; CHECK-NEXT: ret void
}

declare void @llvm.memset.i64(i8*, i8, i64, i32)
declare void @llvm.memcpy.i64(i8*, i8*, i64, i32)

; Should delete store of 10 even though memset is a may-store to P (P and Q may
; alias).
define void @test6(i32 *%p, i8 *%q) {
  store i32 10, i32* %p, align 4       ;; dead.
  call void @llvm.memset.i64(i8* %q, i8 42, i64 900, i32 1)
  store i32 30, i32* %p, align 4
  ret void
; CHECK: @test6
; CHECK-NEXT: call void @llvm.memset
}

; Should delete store of 10 even though memcpy is a may-store to P (P and Q may
; alias).
define void @test7(i32 *%p, i8 *%q, i8* noalias %r) {
  store i32 10, i32* %p, align 4       ;; dead.
  call void @llvm.memcpy.i64(i8* %q, i8* %r, i64 900, i32 1)
  store i32 30, i32* %p, align 4
  ret void
; CHECK: @test7
; CHECK-NEXT: call void @llvm.memcpy
}

; Do not delete stores that are only partially killed.
define i32 @test8() {
        %V = alloca i32
        store i32 1234567, i32* %V
        %V2 = bitcast i32* %V to i8*
        store i8 0, i8* %V2
        %X = load i32* %V
        ret i32 %X
        
; CHECK: @test8
; CHECK: store i32 1234567
}


; Test for byval handling.
%struct.x = type { i32, i32, i32, i32 }
define void @test9(%struct.x* byval  %a) nounwind  {
	%tmp2 = getelementptr %struct.x* %a, i32 0, i32 0
	store i32 1, i32* %tmp2, align 4
	ret void
; CHECK: @test9
; CHECK-NEXT: ret void
}

; va_arg has fuzzy dependence, the store shouldn't be zapped.
define double @test10(i8* %X) {
        %X_addr = alloca i8*
        store i8* %X, i8** %X_addr
        %tmp.0 = va_arg i8** %X_addr, double
        ret double %tmp.0
; CHECK: @test10
; CHECK: store
}


; DSE should delete the dead trampoline.
declare i8* @llvm.init.trampoline(i8*, i8*, i8*)
declare void @test11f()
define void @test11() {
; CHECK: @test11
	%storage = alloca [10 x i8], align 16		; <[10 x i8]*> [#uses=1]
; CHECK-NOT: alloca
	%cast = getelementptr [10 x i8]* %storage, i32 0, i32 0		; <i8*> [#uses=1]
	%tramp = call i8* @llvm.init.trampoline( i8* %cast, i8* bitcast (void ()* @test11f to i8*), i8* null )		; <i8*> [#uses=1]
; CHECK-NOT: trampoline
	ret void
; CHECK: ret void
}


; PR2599 - load -> store to same address.
define void @test12({ i32, i32 }* %x) nounwind  {
	%tmp4 = getelementptr { i32, i32 }* %x, i32 0, i32 0
	%tmp5 = load i32* %tmp4, align 4
	%tmp7 = getelementptr { i32, i32 }* %x, i32 0, i32 1
	%tmp8 = load i32* %tmp7, align 4
	%tmp17 = sub i32 0, %tmp8
	store i32 %tmp5, i32* %tmp4, align 4
	store i32 %tmp17, i32* %tmp7, align 4
	ret void
; CHECK: @test12
; CHECK-NOT: tmp5
; CHECK: ret void
}


; %P doesn't escape, the DEAD instructions should be removed.
declare void @test13f()
define i32* @test13() {
        %p = tail call i8* @malloc(i32 4)
        %P = bitcast i8* %p to i32*
        %DEAD = load i32* %P
        %DEAD2 = add i32 %DEAD, 1
        store i32 %DEAD2, i32* %P
        call void @test13f( )
        store i32 0, i32* %P
        ret i32* %P
; CHECK: @test13()
; CHECK-NEXT: malloc
; CHECK-NEXT: bitcast
; CHECK-NEXT: call void
}

declare noalias i8* @malloc(i32)



define void @test14(i32* %Q) {
        %P = alloca i32
        %DEAD = load i32* %Q
        store i32 %DEAD, i32* %P
        ret void

; CHECK: @test14
; CHECK-NEXT: ret void
}


; PR8701

;; Fully dead overwrite of memcpy.
define void @test15(i8* %P, i8* %Q) nounwind ssp {
  tail call void @llvm.memcpy.i64(i8* %P, i8* %Q, i64 12, i32 1)
  tail call void @llvm.memcpy.i64(i8* %P, i8* %Q, i64 12, i32 1)
  ret void
; CHECK: @test15
; CHECK-NEXT: call void @llvm.memcpy
; CHECK-NEXT: ret
}

;; Full overwrite of smaller memcpy.
define void @test16(i8* %P, i8* %Q) nounwind ssp {
  tail call void @llvm.memcpy.i64(i8* %P, i8* %Q, i64 8, i32 1)
  tail call void @llvm.memcpy.i64(i8* %P, i8* %Q, i64 12, i32 1)
  ret void
; CHECK: @test16
; CHECK-NEXT: call void @llvm.memcpy
; CHECK-NEXT: ret
}

;; Overwrite of memset by memcpy.
define void @test17(i8* %P, i8* %Q) nounwind ssp {
  tail call void @llvm.memset.i64(i8* %P, i8 42, i64 8, i32 1)
  tail call void @llvm.memcpy.i64(i8* %P, i8* %Q, i64 12, i32 1)
  ret void
; CHECK: @test17
; CHECK-NEXT: call void @llvm.memcpy
; CHECK-NEXT: ret
}

