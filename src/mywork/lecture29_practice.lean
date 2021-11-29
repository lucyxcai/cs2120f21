import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type 
  zero : nat --zero is type nat
  succ (n' : nat) : nat --any term of that kind is type nat, applying succ to that nat number gives you another nat number

def z := nat.zero
#check z
#reduce z --evaluates it 
def o := nat.succ z --nat.succ(0)
def t := nat.succ o --nat.succ(1)

def f : nat := 
begin
  exact nat.succ (nat.succ t)
end

#check f
#reduce f 

def inc' : nat → nat :=
begin
  assume n, 
  exact nat.succ n
end

def inc : nat → nat n := 
nat.succ n

#reduce inc f 

def dec : nat → nat 
  (nat.zero) := nat.zero 
  (nat.succ n') := n' 

def add : nat →nat → nat 
  (nat.zero) (m) := m  
  (nat.succ n') (m) := 
  /- answer for n'-/
  nat.succ (add n' m) --1 + n' + m

def mul : nat → nat → nat --multiply
  (nat.zero) (m) := nat.zero
  (nat.succ n') (m) := /- m n' (mul n' m)-/ --multiply n'(0) by m = 0
  add (m) (mul n' m) 

#reduce mul f t --8 = 4 * 2
#reduce mul f f --16 = 4*4




end hidden