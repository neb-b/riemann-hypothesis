module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

section Over

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R']
  {A A'' : Type} [CommRing A] [Bialgebra R A] [CommRing A''] [Bialgebra R'' A'']

def SemiBialgHom.liftOver {ρ : R →+* R''} (f : SemiBialgHom ρ A A'') (τ : R' →+* R'')
    (h : ∀ r, ρ r = τ (algebraMap R R' r)) : SemiBialgHom τ (R' ⊗[R] A) A'' :=
  letI : Algebra R A'' := ((algebraMap R'' A'').comp ρ).toAlgebra
  let f' : A →ₐ[R] A'' := ⟨f.toRingHom, fun r => by
    change f (algebraMap R A r) = algebraMap R'' A'' (ρ r)
    exact f.map_algebraMap r⟩
  let g : R' ⊗[R] A →ₐ[R] A'' := Algebra.TensorProduct.lift
    { (algebraMap R'' A'').comp τ with commutes' := fun r => congrArg (algebraMap R'' A'') (h r).symm }
    f' fun _ _ => .all _ _
  have hg : ∀ r a, g (r ⊗ₜ a) = τ r • f a := fun r a => by
    change algebraMap R'' A'' (τ r) * f a = τ r • f a
    exact (Algebra.smul_def (τ r) (f a)).symm
  have hs : ∀ (r : R') x, g (r • x) = τ r • g x := fun r x => by
    induction x with
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
    | tmul s a => rw [smul_tmul', hg, hg, smul_eq_mul, map_mul, mul_smul]
  { toRingHom := g
    smul_map := hs
    counit_map := fun x => by
      change counit (g x) = _
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul r a =>
        rw [hg, map_smul, f.counit_map, TensorProduct.counit_tmul, h]
        simp [Algebra.smul_def, mul_comm]
    comul_map := fun x => by
      change comul (g x) = _
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul r a =>
        rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', hs, map_smul, map_smul, map_smulₛₗ, hg, map_one,
          one_smul]
        congr 1
        rw [← f.two_comul, TensorProduct.comul_tmul, CommSemiring.comul_apply]
        generalize comul (R := R) a = c
        induction c with
        | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]
        | tmul a b => simp [hg] }

@[simp] theorem SemiBialgHom.liftOver_tmul {ρ : R →+* R''} (f : SemiBialgHom ρ A A'')
    (τ : R' →+* R'') (h : ∀ r, ρ r = τ (algebraMap R R' r)) (r : R') (a : A) :
    f.liftOver τ h (r ⊗ₜ a) = τ r • f a := by
  change algebraMap R'' A'' (τ r) * f a = τ r • f a
  exact (Algebra.smul_def (τ r) (f a)).symm

end Over

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R]

abbrev frobRing (h : (p : R) = 0) : R →+* R := SS.FrobField.powHom R p 1 hp.out h

@[simp] theorem frobRing_apply (h : (p : R) = 0) (r : R) : frobRing h r = r ^ p :=
  congrArg (r ^ ·) (pow_one p)


omit hp in
theorem natCast_eq_zero_of_algebra (h : (p : R) = 0) (A : Type) [CommRing A] [Algebra R A] :
    (p : A) = 0 := by
  rw [← map_natCast (algebraMap R A), h, map_zero]

def frobBialg (h : (p : R) = 0) (A : Type) [CommRing A] [Bialgebra R A] :
    SemiBialgHom (frobRing h) A A where
  toRingHom := frobRing (natCast_eq_zero_of_algebra h A)
  smul_map r a := by simp only [frobRing_apply, smul_pow]
  counit_map a := by simp only [frobRing_apply, counit_pow]
  comul_map a := by
    rw [frobRing_apply, comul_pow, ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A))]
    generalize comul (R := R) a = c
    induction c with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_pow]

@[simp] theorem frobBialg_apply (h : (p : R) = 0) {A : Type} [CommRing A] [Bialgebra R A] (a : A) :
    frobBialg h A a = a ^ p := by
  change frobRing (natCast_eq_zero_of_algebra h A) a = a ^ p
  exact frobRing_apply (natCast_eq_zero_of_algebra h A) a

end Frobenius

end PDiv

namespace PDivGroup

open PDiv

section Over

variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] [Algebra O O']
  {G : PDivGroup p O}

def SemiHom.liftOver {G'' : PDivGroup p O''} {ρ : O →+* O''} (s : SemiHom ρ G'' G) (τ : O' →+* O'')
    (h : ∀ r, ρ r = τ (algebraMap O O' r)) : SemiHom τ G'' (G.baseChange O') :=
  ⟨fun n => (s.app n).liftOver τ h, fun n x => by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r a => simp [s.res_app]⟩

@[simp] theorem SemiHom.liftOver_app {G'' : PDivGroup p O''} {ρ : O →+* O''} (s : SemiHom ρ G'' G)
    (τ : O' →+* O'') (h : ∀ r, ρ r = τ (algebraMap O O' r)) (n : ℕ) (r : O') (a : G.A n) :
    (s.liftOver τ h).app n (r ⊗ₜ[O] a) = τ r • s.app n a := (s.app n).liftOver_tmul τ h r a


variable (O') in
theorem baseChange_induction (n : ℕ) {P : (G.baseChange O').A n → Prop} (h0 : P 0)
    (h1 : ∀ (r : O') a, P (r • (G.toBase O').app n a)) (h2 : ∀ x y, P x → P y → P (x + y))
    (x : (G.baseChange O').A n) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact h2 x y hx hy
  | tmul r a =>
    have e : r • (G.toBase O').app n a = r ⊗ₜ[O] a := by rw [toBase_app, smul_tmul', smul_eq_mul, mul_one]
    exact e ▸ h1 r a

variable [Fact p.Prime]

theorem dualBaseChange_toBase (n : ℕ) (χ : CartierDual O (G.A n)) (a : G.A n) :
    ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv
      ((G.toBase O').app n a) = algebraMap O O' (χ a) := by
  change CartierDual.baseChange O O' (G.A n) (1 ⊗ₜ χ) (1 ⊗ₜ a) = _
  rw [CartierDual.baseChange_tmul_tmul, one_mul, Algebra.algebraMap_eq_smul_one]

theorem baseChange_ext_dual (n : ℕ) {x y : (G.baseChange O').A n}
    (h : ∀ χ : CartierDual O (G.A n),
      ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv x =
      ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv y) : x = y := by
  refine CartierDual.eq_of_forall_apply (R := O') fun φ => ?_
  obtain ⟨z, rfl⟩ : ∃ z, (PerfdLat.dualBaseChange O' G).hom.app n z = φ :=
    (CartierDual.baseChange O O' (G.A n)).surjective φ
  induction z using baseChange_induction O' (G := G.dual) n with
  | h0 => simp
  | h1 r χ => rw [map_smul, ofConv_smul, LinearMap.smul_apply, LinearMap.smul_apply, h]
  | h2 z w hz hw => rw [map_add (f := _), ofConv_add, LinearMap.add_apply, LinearMap.add_apply, hz, hw]

end Over

variable {p : ℕ} [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S] (h : (p : R) = 0)
  (G : PDivGroup p R) {H K : PDivGroup p R}

def absFrob : SemiHom (frobRing h) G G :=
  ⟨fun n => frobBialg h (G.A n), fun n a => by simp only [frobBialg_apply, map_pow]⟩

@[simp] theorem absFrob_app (n : ℕ) (a : G.A n) : (absFrob h G).app n a = a ^ p :=
  frobBialg_apply h a

def frobTwist : PDivGroup p R :=
  letI := (frobRing h).toAlgebra
  G.baseChange R

@[simp] theorem frobTwist_height : (frobTwist h G).height = G.height := rfl

def frobProj : SemiHom (frobRing h) (frobTwist h G) G :=
  letI := (frobRing h).toAlgebra
  G.toBase R


variable {G} in
def frobLift (s : SemiHom (frobRing h) H G) : H ⟶ frobTwist h G :=
  letI := (frobRing h).toAlgebra
  SemiHom.lift (O := R) (O' := R) s


variable {G} in
@[simp] theorem frobLift_app_frobProj (s : SemiHom (frobRing h) H G) (n : ℕ) (a : G.A n) :
    (frobLift h s).app n ((frobProj h G).app n a) = s.app n a :=
  letI := (frobRing h).toAlgebra
  (SemiHom.lift_app (O := R) (O' := R) s n 1 a).trans (one_smul _ _)

def relFrob : G ⟶ frobTwist h G := frobLift h (absFrob h G)

def frobTwistDual : (frobTwist h G).dual ≅ frobTwist h G.dual :=
  letI := (frobRing h).toAlgebra
  PerfdLat.dualBaseChange R G

def verschiebung : frobTwist h G ⟶ G :=
  (frobTwist h G).bidual.hom ≫
    dualHom _ _ (relFrob h G.dual ≫ (frobTwistDual h G).inv) ≫ G.bidual.inv

variable {G}

theorem frobTwist_induction (n : ℕ) {P : (frobTwist h G).A n → Prop} (h0 : P 0)
    (h1 : ∀ (r : R) a, P (r • (frobProj h G).app n a)) (h2 : ∀ x y, P x → P y → P (x + y))
    (x : (frobTwist h G).A n) : P x :=
  letI := (frobRing h).toAlgebra
  baseChange_induction R n h0 h1 h2 x

theorem frobTwist_hom_ext {f g : H ⟶ frobTwist h G}
    (e : ∀ n a, f.app n ((frobProj h G).app n a) = g.app n ((frobProj h G).app n a)) : f = g :=
  letI := (frobRing h).toAlgebra
  baseChange_hom_ext e

@[simp] theorem relFrob_app_frobProj (n : ℕ) (a : G.A n) :
    (relFrob h G).app n ((frobProj h G).app n a) = a ^ p :=
  (frobLift_app_frobProj h _ n a).trans (absFrob_app h G n a)

theorem frobTwistDual_frobProj (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv
      ((frobProj h G).app n a) = χ a ^ p :=
  letI := (frobRing h).toAlgebra
  (dualBaseChange_toBase (O' := R) n χ a).trans (frobRing_apply h _)

theorem frobTwist_ext_dual (n : ℕ) {x y : (frobTwist h G).A n}
    (e : ∀ χ : CartierDual R (G.A n),
      ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv x =
      ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv y) : x = y :=
  letI := (frobRing h).toAlgebra
  baseChange_ext_dual (O' := R) n e

theorem frobTwistDual_verschiebung (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv
      ((verschiebung h G).app n a) = (χ ^ p) a := by
  refine (CartierDual.apply_bidual_symm _ _).trans ?_
  change ((relFrob h G.dual).app n (((frobTwistDual h G).inv ≫ (frobTwistDual h G).hom).app n
    ((frobProj h G.dual).app n χ))).ofConv a = _
  rw [Iso.inv_hom_id]
  exact congrArg (fun φ : CartierDual R (G.A n) => φ a) (relFrob_app_frobProj h (G := G.dual) n χ)

def SemiHom.frobTwist (h' : (p : S) = 0) {σ : R →+* S} {G' : PDivGroup p S} (s : SemiHom σ G' G) :
    SemiHom σ (frobTwist h' G') (frobTwist h G) :=
  letI := (frobRing h).toAlgebra
  ((frobProj h' G').comp s).liftOver σ fun r =>
    (frobRing_apply h' _).trans ((map_pow σ r p).symm.trans (congrArg σ (frobRing_apply h r).symm))

@[simp] theorem SemiHom.frobTwist_app_frobProj (h' : (p : S) = 0) {σ : R →+* S}
    {G' : PDivGroup p S} (s : SemiHom σ G' G) (n : ℕ) (a : G.A n) :
    (s.frobTwist h h').app n ((frobProj h G).app n a) = (frobProj h' G').app n (s.app n a) :=
  letI := (frobRing h).toAlgebra
  (SemiHom.liftOver_app ((frobProj h' G').comp s) σ _ n 1 a).trans
    (by rw [map_one, one_smul, SemiHom.comp_app])

section BaseChange

variable (h' : (p : S) = 0) [Algebra R S] (G)

end BaseChange

end PDivGroup

end GlobalTheory
