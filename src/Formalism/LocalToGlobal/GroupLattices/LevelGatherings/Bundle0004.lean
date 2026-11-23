module

public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle0003
public import Formalism.LocalRingCardinality.DataKerI

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapE
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

section Single

variable (F : Type) [Field F] [NumberField F]

theorem adele_ext {x y : FiniteAdeleRing (𝓞 F) F} (h : ∀ v, evalV F v x = evalV F v y) : x = y := by
  exact Subtype.ext (funext fun v => h v)


open Classical in
def sglFun (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨Pi.single w a, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset ?_)
    intro v hv
    by_contra hne
    apply hv
    have : v ≠ w := hne
    rw [Pi.single_eq_of_ne this]
    exact zero_mem _⟩

theorem sgl_same (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : evalV F w (sglFun F w a) = a := by
  classical
  show (Pi.single w a : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) w = a
  exact Pi.single_eq_same w a

theorem sgl_ne (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    evalV F v (sglFun F w a) = 0 := by
  classical
  show (Pi.single w a : (u : HeightOneSpectrum (𝓞 F)) → u.adicCompletion F) v = 0
  exact Pi.single_eq_of_ne h a

def sgl (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun := sglFun F w
  map_add' a b := by
    apply adele_ext
    intro v
    rw [map_add (f := _)]
    by_cases h : v = w
    · subst h; simp only [sgl_same]
    · simp only [sgl_ne F w _ h, add_zero]
  map_smul' c a := by
    apply adele_ext
    intro v
    rw [RingHom.id_apply, map_smul]
    by_cases h : v = w
    · subst h; simp only [sgl_same]
    · simp only [sgl_ne F w _ h, smul_zero]

theorem sgl_apply_same (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : evalV F w (sgl F w a) = a := sgl_same F w a

theorem sgl_apply_ne (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    evalV F v (sgl F w a) = 0 := sgl_ne F w a h

theorem sgl_mul (w : HeightOneSpectrum (𝓞 F)) (a b : w.adicCompletion F) : sgl F w (a * b) = sgl F w a * sgl F w b := by
  apply adele_ext
  intro v
  rw [map_mul (evalV F v)]
  by_cases h : v = w
  · subst h; simp only [sgl_apply_same]
  · simp only [sgl_apply_ne F w _ h, mul_zero]

variable (E : Type) [Field E] [Algebra F E]

def iE (w : HeightOneSpectrum (𝓞 F)) : E ⊗[F] w.adicCompletion F →ₗ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  LinearMap.lTensor E (sgl F w)

theorem iE_tmul (w : HeightOneSpectrum (𝓞 F)) (e : E) (a : w.adicCompletion F) :
    iE F E w (e ⊗ₜ[F] a) = e ⊗ₜ[F] sgl F w a := LinearMap.lTensor_tmul E (sgl F w) e a

theorem iE_mul (w : HeightOneSpectrum (𝓞 F)) (x y : E ⊗[F] w.adicCompletion F) :
    iE F E w (x * y) = iE F E w x * iE F E w y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul e a =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | tmul e' b => simp only [Algebra.TensorProduct.tmul_mul_tmul, iE_tmul, sgl_mul]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy']
  | add x x' hx hx' => simp only [add_mul, map_add (f := _), hx, hx']

theorem prV_iE_same (w : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] w.adicCompletion F) : prV (E := E) w (iE F E w x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e a => simp [prV, iE_tmul, sgl_apply_same]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem prV_iE_ne (w : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] w.adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    prV (E := E) v (iE F E w x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e a => simp [prV, iE_tmul, sgl_apply_ne F w a h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem sig_iE (σE : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] w.adicCompletion F) :
    sigR σE (FiniteAdeleRing (𝓞 F) F) (iE F E w x) = iE F E w (sigR σE (w.adicCompletion F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e a => simp [sigR, iE_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def epsW (w : HeightOneSpectrum (𝓞 F)) : E ⊗[F] FiniteAdeleRing (𝓞 F) F := iE F E w 1

theorem epsW_idem (w : HeightOneSpectrum (𝓞 F)) : epsW F E w * epsW F E w = epsW F E w := by
  show iE F E w 1 * iE F E w 1 = iE F E w 1
  rw [← iE_mul, mul_one]

theorem epsW_mul_iE (w : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] w.adicCompletion F) :
    epsW F E w * iE F E w x = iE F E w x := by
  show iE F E w 1 * iE F E w x = iE F E w x
  rw [← iE_mul, one_mul]

theorem epsW_mul_incl (w : HeightOneSpectrum (𝓞 F)) (e : E) :
    epsW F E w * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e = iE F E w (inclE (F := F) (w.adicCompletion F) e) := by
  show iE F E w 1 * _ = _
  simp only [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.one_def, iE_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end Single

section Section

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (w : HeightOneSpectrum (𝓞 F))

def mapE (X : Matrix n n (E ⊗[F] w.adicCompletion F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  X.map (iE F E w)

theorem mapE_mul (X Y : Matrix n n (E ⊗[F] w.adicCompletion F)) :
    mapE F E w (X * Y) = mapE F E w X * mapE F E w Y := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mapE, Matrix.map_apply, Matrix.mul_apply, map_sum, iE_mul]

theorem eps_smul_mapE (X : Matrix n n (E ⊗[F] w.adicCompletion F)) : epsW F E w • mapE F E w X = mapE F E w X := by
  ext i j
  simp only [mapE, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, epsW_mul_iE]

theorem compl_smul_mapE (X : Matrix n n (E ⊗[F] w.adicCompletion F)) : (1 - epsW F E w) • mapE F E w X = 0 := by
  ext i j
  simp only [mapE, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, sub_mul, one_mul, epsW_mul_iE, sub_self,
    Matrix.zero_apply]

theorem mapE_one : mapE F E w (1 : Matrix n n (E ⊗[F] w.adicCompletion F)) = epsW F E w • 1 := by
  ext i j
  simp only [mapE, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp [epsW]

def secM : Matrix n n (E ⊗[F] w.adicCompletion F) →* Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  toFun X := (1 - epsW F E w) • 1 + mapE F E w X
  map_one' := by rw [mapE_one, ← add_smul, sub_add_cancel, one_smul]
  map_mul' X Y := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
      smul_smul, compl_idem _ (epsW_idem F E w), compl_smul_mapE, add_zero, zero_add, mapE_mul]

def sec : GL n (E ⊗[F] w.adicCompletion F) →* GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Units.map (secM F E w)

theorem sec_val (X : GL n (E ⊗[F] w.adicCompletion F)) :
    (sec F E w X : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (1 - epsW F E w) • 1 + mapE F E w (X : Matrix n n (E ⊗[F] w.adicCompletion F)) := rfl

theorem prV_epsW_same : prV (E := E) w (epsW F E w) = 1 := prV_iE_same F E w 1

theorem prV_epsW_ne {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : prV (E := E) v (epsW F E w) = 0 := prV_iE_ne F E w 1 h

theorem bc_sec_same (X : GL n (E ⊗[F] w.adicCompletion F)) : bc (prV (E := E) w) (sec F E w X) = X := by
  apply Units.ext
  show (RingHom.mapMatrix (prV (E := E) w)) (sec F E w X : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
    (X : Matrix n n (E ⊗[F] w.adicCompletion F))
  rw [sec_val]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mapE,
    map_add, map_mul, map_sub, map_one, prV_epsW_same, prV_iE_same, sub_self, zero_mul, zero_add]

theorem bc_sec_ne (X : GL n (E ⊗[F] w.adicCompletion F)) {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    bc (prV (E := E) v) (sec F E w X) = 1 := by
  apply Units.ext
  show (RingHom.mapMatrix (prV (E := E) v)) (sec F E w X : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
    ((1 : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F))
  rw [sec_val, Units.val_one]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mapE,
    map_add, map_mul, map_sub, map_one, prV_epsW_ne F E w h, prV_iE_ne F E w _ h, sub_zero, one_mul, add_zero]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

theorem sec_mem_UPts (σE : E →ₐ[F] E) (J : Matrix n n E) {X : GL n (E ⊗[F] w.adicCompletion F)}
    (hX : X ∈ UPts σE J (w.adicCompletion F)) : sec F E w X ∈ UPts σE J (FiniteAdeleRing (𝓞 F) F) := by
  have hX' : cT (sigR σE (w.adicCompletion F)) (X : Matrix n n (E ⊗[F] w.adicCompletion F)) *
      J.map (inclE (F := F) (w.adicCompletion F)) * (X : Matrix n n (E ⊗[F] w.adicCompletion F)) =
      J.map (inclE (F := F) (w.adicCompletion F)) := hX
  show cT (sigR σE (FiniteAdeleRing (𝓞 F) F)) (sec F E w X : Matrix n n _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (sec F E w X : Matrix n n _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
  have hσ : sigR σE (FiniteAdeleRing (𝓞 F) F) (epsW F E w) = epsW F E w := by
    rw [epsW, sig_iE, map_one]
  have hc : cT (sigR σE (FiniteAdeleRing (𝓞 F) F)) (sec F E w X : Matrix n n _) =
      (1 - epsW F E w) • 1 + mapE F E w (cT (sigR σE (w.adicCompletion F)) (X : Matrix n n _)) := by
    rw [sec_val]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [cT, mapE, hσ, sig_iE]
    · simp [cT, mapE, hσ, sig_iE, Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]
  have hJ : epsW F E w • J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) =
      mapE F E w (J.map (inclE (F := F) (w.adicCompletion F))) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mapE, epsW_mul_incl]
  have hmid : ∀ Y Z : Matrix n n (E ⊗[F] w.adicCompletion F),
      mapE F E w Y * J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * mapE F E w Z =
        mapE F E w (Y * J.map (inclE (F := F) (w.adicCompletion F)) * Z) := by
    intro Y Z
    rw [mapE_mul, mapE_mul, ← hJ, Matrix.mul_smul, ← Matrix.smul_mul, eps_smul_mapE]
  rw [hc, sec_val]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hmid, hX', ← hJ]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, compl_idem _ (epsW_idem F E w)]
  have h1 : (1 - epsW F E w) • (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * mapE F E w (X : Matrix n n _)) = 0 := by
    rw [← Matrix.mul_smul, compl_smul_mapE, Matrix.mul_zero]
  have h2 : (1 - epsW F E w) • (mapE F E w (cT (sigR σE (w.adicCompletion F)) (X : Matrix n n _)) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) = 0 := by
    rw [← Matrix.smul_mul, compl_smul_mapE, Matrix.zero_mul]
  rw [h1, h2, add_zero, zero_add, ← add_smul, sub_add_cancel, one_smul]

end Section

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_mul {R : Ranks} (H : Host R) (g g' : R.GG) (x : H.E) : H.emb (g * g') x = H.emb g (H.sigmaOf g' x) := by
  show H.φ₀ ((H.sigmaOf (g * g')) x) = H.φ₀ ((H.sigmaOf g) ((H.sigmaOf g') x))
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_mul, AlgEquiv.mul_apply]

theorem sigmaOf_pow {R : Ranks} (H : Host R) (g : R.GG) (s : ℕ) (x : H.E) :
    H.sigmaOf (g ^ s) x = ((H.sigmaOf g) ^ s) x := by
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_pow]

variable {p : ℕ} [Fact p.Prime] {W Qq Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [Field Kf]

def PosCompat {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  ∀ (v : Fin (nOrb (zPsi R.toFrame h))) (s : Fin (orderOf (zPsi R.toFrame h))) (x : H.E),
    iK (ι ((σ ^ s.val) (iw v x))) =
      lamV lam (H.emb (((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val) x)

theorem posCompat_of_base {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p])
    (hbase : ∀ v x, iK (ι (iw v x)) = lamV lam (H.emb ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) x))
    (hfrob : ∀ v x, σ (iw v x) = iw v (H.sigmaOf ((c0, h) : R.GG) x)) :
    PosCompat H h ι σ iw iK lam := by
  intro v s x
  have key : ∀ (k : ℕ) (y : H.E), (σ ^ k) (iw v y) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ]
      show (σ ^ k) (σ (iw v y)) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) (H.sigmaOf ((c0, h) : R.GG) y))
      rw [hfrob, ih]
  have e1 : ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val =
      ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) * ((c0, h) : R.GG) ^ s.val := by
    rw [posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc]
    congr 1
    show ((1, h) : R.GG) ^ s.val * (c0, 1) ^ s.val = ((c0, h) : R.GG) ^ s.val
    ext <;> simp
  rw [e1, emb_mul, sigmaOf_pow, key, hbase]

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev gatOfLevelP (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) : GAtP p :=
  gatOfLevel L hS nV r lam0 dom hk I ψ (repP L p) e

end Level

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev gatRecP (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) : GAtP p :=
  gatRec D u h hS r L I ψ (repP L p) e

def gatRecP_lev (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) :
    Formalism.L2.Herm.GLevTie L (gatRecP D u h hS r L I ψ e) :=
  gatRec_lev D u h hS r L I ψ (repP L p) e (repP_mk L p) (repP_over L p)

end Record

end Formalism.L2.G
end
end

