module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmBc
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.FramesTr
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

theorem frames_tr' (emb : Tau → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) (z' : Frames (gramC J emb)) : ∃ z : Frames (gramC J emb), IsTr (atInf emb γ) z' z := by
  refine ⟨Subtype.mk (fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * z'.1 τ) (fun τ => ?_), fun τ => rfl⟩
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ (z'.2 τ)
  have hdet : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det = emb τ (γ : Matrix (Fin n) (Fin n) E).det := by
    rw [RingHom.map_det]; rfl
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).map (emb τ)

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def PtAll : Prop :=
  ∀ c : cls, ∃ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U),
    γ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1)

variable {S emb embLL G e A pos embV yc}

theorem cmpC_rat (x : V) : RatFn G e (cmpC S emb embLL G e A pos embV yc x) := by
  delta RatFn RatFnP
  intro i L
  by_cases h : G.P.IsLatTup L
  · exact ⟨valC S emb embLL G A pos embV yc x i L, by simp [cmpC, h]⟩
  · exact ⟨0, by simp [cmpC, h]⟩

private theorem isLatTup_colSpan_GL (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    G.P.IsLatTup (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) := by
  intro v
  exact Exists.intro (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))
    ⟨(Matrix.isUnit_iff_isUnit_det _).mp (g v).isUnit, rfl⟩

theorem cmpC_inj (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hex : ValEx S emb embLL G A pos embV yc)
    (hall : PtAll S G A yc) (hinj : Function.Injective embV) (x : V)
    (hx : cmpC S emb embLL G e A pos embV yc x = 0) : x = 0 := by
  apply hinj
  rw [map_zero]
  funext c z'
  obtain ⟨i, g, γ, κ, hγ, hpt⟩ := hall c
  obtain ⟨z, hz⟩ := frames_tr' emb hc γ hγ z'
  have hL := isLatTup_colSpan_GL (G := G) g
  obtain ⟨Q, hQ⟩ := hex x i (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) hL
  have hv : IsVal S emb embLL G A pos embV yc x i (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
      (valC S emb embLL G A pos embV yc x i
      (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))) := by
    have h' : ∃ Q, IsVal S emb embLL G A pos embV yc x i
        (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) Q := ⟨Q, hQ⟩
    unfold valC
    rw [dite_eq_left h']
    exact Classical.choose_spec h'
  have h0 : valC S emb embLL G A pos embV yc x i
      (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) = 0 := by
    have h1 : cmpC S emb embLL G e A pos embV yc x i
        (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) = 0 := by
      rw [hx]; rfl
    simp only [cmpC, if_pos hL] at h1
    exact MvPolynomial.map_injective e e.injective (by rw [h1, map_zero])
  rw [h0] at hv
  unfold IsVal at hv
  have h2 := hv.2 g (fun v => rfl) c γ hγ κ hpt z z' hz
  simp only [map_zero, Pi.zero_apply] at h2
  simp only [Pi.zero_apply]
  exact (mul_eq_zero.mp h2.symm).resolve_left (by simp)

private theorem isVal_add {x y : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P LL}
    (h : IsVal S emb embLL G A pos embV yc x i L Q) (h' : IsVal S emb embLL G A pos embV yc y i L Q') :
    IsVal S emb embLL G A pos embV yc (x + y) i L (Q + Q') := by
  unfold IsVal at *
  refine ⟨Submodule.add_mem _ h.1 h'.1, fun g hg c γ hγ κ hpt z z' hz => ?_⟩
  simp only [map_add (f := _), Pi.add_apply, mul_add]
  rw [h.2 g hg c γ hγ κ hpt z z' hz, h'.2 g hg c γ hγ κ hpt z z' hz]

private theorem isVal_smul {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P LL} (a : LL)
    (h : IsVal S emb embLL G A pos embV yc x i L Q) :
    IsVal S emb embLL G A pos embV yc (a • x) i L (a • Q) := by
  unfold IsVal at *
  refine ⟨Submodule.smul_mem _ a h.1, fun g hg c γ hγ κ hpt z z' hz => ?_⟩
  have hm : MvPolynomial.map embLL (a • Q) = (embLL a) • MvPolynomial.map embLL Q := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.smul_eq_C_mul]
  rw [hm, map_smul, Pi.smul_apply, h.2 g hg c γ hγ κ hpt z z' hz, map_smulₛₗ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem isVal_valC_of_isLatTup (hex : ValEx S emb embLL G A pos embV yc) (x : V) (i : G.comp) {L : G.P.Tup}
    (hL : G.P.IsLatTup L) : IsVal S emb embLL G A pos embV yc x i L (valC S emb embLL G A pos embV yc x i L) := by
  have h' := hex x i L hL
  unfold valC
  rw [dite_eq_left h']
  exact Classical.choose_spec h'

theorem cmpC_li (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hex : ValEx S emb embLL G A pos embV yc)
    (hu : ValUniq S emb embLL G A pos embV yc) (hall : PtAll S G A yc) (hinj : Function.Injective embV)
    {ι : Type} (b : ι → V) (hb : LinearIndependent LL b) :
    LinearIndependent G.Kf fun a => cmpC S emb embLL G e A pos embV yc (b a) := by
  let Φ : V →ₗ[LL] (G.comp → {L : G.P.Tup // G.P.IsLatTup L} → XR G.P LL) :=
    { toFun := fun x i L => valC S emb embLL G A pos embV yc x i L.1
      map_add' := fun x y => by
        funext i L
        exact hu (x + y) i L.1 _ _ L.2 (isVal_valC_of_isLatTup hex (x + y) i L.2)
          (isVal_add (isVal_valC_of_isLatTup hex x i L.2) (isVal_valC_of_isLatTup hex y i L.2))
      map_smul' := fun a x => by
        funext i L
        exact hu (a • x) i L.1 _ _ L.2 (isVal_valC_of_isLatTup hex (a • x) i L.2)
          (isVal_smul a (isVal_valC_of_isLatTup hex x i L.2)) }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine cmpC_inj (e := e) hc hex hall hinj x ?_
    funext i L
    by_cases hL : G.P.IsLatTup L
    · have h3 := congrFun (congrFun hx i) ⟨L, hL⟩
      simp only [cmpC, if_pos hL, Pi.zero_apply]
      rw [show valC S emb embLL G A pos embV yc x i L = 0 from h3, map_zero]
    · simp only [cmpC, if_neg hL, Pi.zero_apply]
  have hw := hb.map' Φ hΦ
  letI : Algebra LL G.Kf := e.toAlgebra
  have hsm : ∀ (q : LL) (y : G.Kf), y * e q = q • y := fun q y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
  let β := Module.Basis.ofVectorSpace LL G.Kf
  rw [linearIndependent_iff']
  rw [linearIndependent_iff'] at hw
  intro s g hg a ha
  have key : ∀ k, ∀ a ∈ s, β.repr (g a) k = 0 := by
    intro k
    apply hw s (fun a => β.repr (g a) k)
    ext i L m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) (congrFun (congrFun hg i) L.1)
    simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, Pi.zero_apply, MvPolynomial.coeff_zero, cmpC, if_pos L.2, MvPolynomial.coeff_map] at h1
    have h2 := congrArg (fun y => β.repr y k) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, Finset.sum_apply', Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply,
      hsm, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [← h2]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h4 : β.repr (g a) = 0 := Finsupp.ext fun k => key k a ha
  exact β.repr.map_eq_zero_iff.mp h4

end Formalism.L2.G.Cmp

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsLatTupSmulIff
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem isLatTup_smul_iff {p : ℕ} {G : GAtP p} (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) :
    G.P.IsLatTup ((G.lev i).smul γ L) ↔ G.P.IsLatTup L := by
  constructor
  · intro h v
    obtain ⟨g', hg', hL⟩ := h v
    refine ⟨(((G.lev i).act v γ)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)).1 * g', ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((G.lev i).act v γ)⁻¹.isUnit).mul hg'
    · have hinj : Function.Injective ((Matrix.mulVecLin (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
          Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))).restrictScalars (G.P.W v)) :=
        Matrix.mulVec_injective_of_isUnit ((G.lev i).act v γ).isUnit
      apply Submodule.map_injective_of_injective hinj
      rw [colSpan_map, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      exact hL
  · intro h v
    obtain ⟨g, hg, hL⟩ := h v
    refine ⟨((G.lev i).act v γ).1 * g, ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((G.lev i).act v γ).isUnit).mul hg
    · show (L v).map _ = _
      rw [hL, colSpan_map]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module LL V] {embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem valC_equiv (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc)
    (x : V) (i : G.comp) (γ : (G.lev i).Γ) (hγ : A.gamI i γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (hκ : A.IsAway i γ κ.1)
    (r : LL) (hr : embLL r = (S.chi κ : ℂ)) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    r • valC S emb embLL G A pos embV yc x i ((G.lev i).smul γ L) =
      natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) (valC S emb embLL G A pos embV yc x i L) := by
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ₀, κ₀, hγ₀, hpt⟩ := hp i g
  apply MvPolynomial.map_injective embLL embLL.injective
  apply sub_eq_zero.1
  apply hi
  funext z
  obtain ⟨z₁, hz₁⟩ := frames_tr emb hc (A.gamI i γ) hγ z
  obtain ⟨z₂, hz₂⟩ := frames_tr emb hc γ₀ hγ₀ z₁
  have h := (cmpC_tie (e := e) tE hex hpos hchi).val_equiv htE hBs hA x i L g hg γ hγ κ hκ c γ₀ hγ₀ κ₀ hpt z z₁ z₂ hz₁ hz₂
  rw [map_sub, Pi.sub_apply, map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr]
  exact sub_eq_zero.2 h

theorem cmpC_equiv (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc)
    (hU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J)
    (haw : ∀ i (γ : (G.lev i).Γ), ∃ κ : S.U, A.IsAway i γ κ.1)
    (x : V) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) :
    cmpC S emb embLL G e A pos embV yc x i ((G.lev i).smul γ L) =
      ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (cmpC S emb embLL G e A pos embV yc x i L) := by
  unfold cmpC
  by_cases hL : G.P.IsLatTup L
  · have hL' : G.P.IsLatTup ((G.lev i).smul γ L) := (isLatTup_smul_iff i γ L).2 hL
    obtain ⟨κ, hκ⟩ := haw i γ
    obtain ⟨r, hr, hr1⟩ := hchi i γ κ hκ
    rw [ite_eq_left hL, ite_eq_left hL', actX_map A tE pos e hA hpos i γ,
      ← valC_equiv tE htE hc hBs hA hex hpos hchi hi hp x i γ (hU i γ) κ hκ r hr L hL, map_smul',
      ← algebraMap_smul G.Kf ((G.lev i).χ γ : G.O), smul_smul, hr1, one_smul]
  · have hL' : ¬ G.P.IsLatTup ((G.lev i).smul γ L) := fun h => hL ((isLatTup_smul_iff i γ L).1 h)
    rw [ite_eq_right hL, ite_eq_right hL', map_zero, smul_zero]

end Formalism.L2.G.Cmp

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOf
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatX (ξ : G.P.Xsp) : Prop := ∃ Q : MvPolynomial _ LL, MvPolynomial.map e Q = ξ

def RatActG : Prop := ∀ (i : G.comp) (γ : (G.lev i).Γ) (ξ : G.P.Xsp), RatX G e ξ →
  RatX G e (((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ)

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def RatInU : Prop := ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J →
  bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)

def AdExt : Prop := ∀ x : V, ∃ fa ∈ AdFun S emb, ∀ c, fa (yc c) = embV x c

def PtOne : Prop :=
  ∀ (i : G.comp) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    (∀ v, L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = x.1 * κ.1 ∧ (S.chi κ : ℂ) = 1

def EvRatPt : Prop :=
  ∀ (x : V) (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    ∃ Q ∈ VtupR G.P LL, ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
      evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = (S.chi κ : ℂ) * embV x c z'

variable {S emb embLL G A pos embV yc}

theorem ratInU : RatInU (F := F) (σ := σ) (J := J) := fun γ hγ =>
  Formalism.UG.P.rational_points_le_holds F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩

theorem atInf_one (emb : Tau → E →+* ℂ) : atInf emb ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
  funext τ
  simp [atInf, Matrix.map_one]

theorem isTr_one (z : Frames (gramC J emb)) : IsTr (atInf emb ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) z z := by
  intro τ
  rw [atInf_one, Matrix.one_mul]

def ptU (hU : RatInU (F := F) (σ := σ) (J := J)) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U) : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 * κ.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU γ hγ) y.2) ((S.U_eq κ.1).1 κ.2).1⟩

theorem valEx_of (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hU : RatInU (F := F) (σ := σ) (J := J))
    (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc) (hO : PtOne S G A) (hR : EvRatPt S emb embLL G A pos embV) :
    ValEx S emb embLL G A pos embV yc := by
  intro x i L hL
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hP i g
  obtain ⟨Q, hQV, hQ⟩ := hR x c γ hγ κ
  obtain ⟨fa, hfa, hfac⟩ := hA x
  let x0 := ptU (S := S) hU γ hγ (yc c) κ
  have key : ∀ z, evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = fa x0 z := by
    intro z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [hQ z z' hz', hfa γ hγ (yc c) x0 κ rfl z z' hz', hfac c]
  refine ⟨Q, hQV, fun g' hg' c' γ' hγ' κ' hpt' z z' hz' => ?_⟩
  let x1 := ptU (S := S) hU γ' hγ' (yc c') κ'
  obtain ⟨κ0, h01, hχ⟩ := hO i L g g' x0 x1 hg hg' hpt hpt'
  have e1 : fa x1 z = (S.chi κ0 : ℂ) * fa x0 z :=
    hfa 1 (Subgroup.one_mem _) x0 x1 κ0 (by rw [map_one, one_mul]; exact h01) z z (isTr_one z)
  have e2 : fa x1 z = (S.chi κ' : ℂ) * fa (yc c') z' := hfa γ' hγ' (yc c') x1 κ' rfl z z' hz'
  rw [key, ← hfac c', ← e2, e1, hχ, one_mul]

theorem valEx_of' (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (hR : EvRatPt S emb embLL G A pos embV) : ValEx S emb embLL G A pos embV yc :=
  valEx_of hc ratInU hA hP hO hR


variable (S emb embLL G A pos embV yc) in
def EvRatRep : Prop :=
  ∀ (x : V) (c : cls), ∃ Q ∈ VtupR G.P LL, ∀ z : Frames (gramC J emb),
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = embV x c z


variable (S embLL) in
def ChiRatAll : Prop := ∀ κ : S.U, ∃ r : LL, embLL r = (S.chi κ : ℂ)


variable (G A pos) in
def VtupStab (tE : Tau → E →+* LL) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ Q ∈ VtupR G.P LL,
    natActR G.P LL (blkLL A σ tE pos γ) Q ∈ VtupR G.P LL

section Stab

variable {p' : ℕ} {O' Kf' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf'] [Algebra O' Kf']
  (P : Places p' O' Kf')

theorem substR_rename (R : Type) [CommRing R] (h : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (v : Fin P.nV) (F : MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) R) :
    substR P R h (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P)) F) =
      MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P)) (Formalism.GradedWeylDivisibility.blockAct R (h v) F) := by
  have e : (substR P R h).comp (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P))) =
      (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P))).comp (Formalism.GradedWeylDivisibility.blockAct R (h v)) := by
    apply MvPolynomial.algHom_ext
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [substR, Formalism.GradedWeylDivisibility.blockAct, map_sum]
  exact congrArg (fun f => f F) e


set_option maxHeartbeats 1000000 in
theorem natActR_VtupR (R : Type) [Field R] (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R)
    (hQ : Q ∈ VtupR P R) : natActR P R g Q ∈ VtupR P R := by
  unfold VtupR at hQ ⊢
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun v => Formalism.MainNotions.G.LatticeSystems.je_rho R (P.lam0 v) (fun s => (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v),
      fun v => Formalism.MainNotions.G.LatticeSystems.je_V R (P.lam0 v) _ (F v) (hF v), ?_⟩
    unfold natActR
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    simp only [substR_rename]
    rw [Finset.prod_congr rfl (fun v _ => (Finset.prod_congr rfl fun s _ => rfl :
      ∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s)) =
        ∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s))))]
    rw [Formalism.MainNotions.G.LatticeSystems.je_prod_smul]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hb : (fun s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) R) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) =
        fun s => ((g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R))⁻¹ :=
      funext fun s => Matrix.coe_units_inv (g v s)
    have e2 : Formalism.MainNotions.G.LatticeSystems.je_rho R (P.lam0 v) (fun s => (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v) =
        (∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s))) •
          Formalism.GradedWeylDivisibility.blockAct R (fun s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) R) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v) := by
      rw [hb]
      rfl
    rw [e2, map_smul]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end Stab

theorem vtupStab (tE : Tau → E →+* LL) : VtupStab G A pos tE (σ := σ) (J := J) :=
  fun _ _ Q hQ => natActR_VtupR G.P LL _ Q hQ

theorem evRatPt_of (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (h1 : EvRatRep emb embLL G A pos embV)
    (h2 : ChiRatAll S embLL) (h3 : VtupStab G A pos tE (σ := σ) (J := J)) : EvRatPt S emb embLL G A pos embV := by
  intro x c γ hγ κ
  obtain ⟨Qc, hQcV, hQc⟩ := h1 x c
  obtain ⟨r, hr⟩ := h2 κ
  refine ⟨r • natActR G.P LL (blkLL A σ tE pos γ) Qc, Submodule.smul_mem _ r (h3 γ hγ Qc hQcV), fun z z' hz => ?_⟩
  have hb := evC_blk A tE pos emb embLL htE γ (unit_of_std A.B γ hBs hγ) (gramC J emb) z' z hz Qc
  rw [map_smul' embLL r, map_smul, Pi.smul_apply, hb, hQc, hr, smul_eq_mul]

theorem valEx_of_rep (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (h1 : EvRatRep emb embLL G A pos embV) (h2 : ChiRatAll S embLL) (h3 : VtupStab G A pos tE (σ := σ) (J := J)) :
    ValEx S emb embLL G A pos embV yc :=
  valEx_of' hc hA hP hO (evRatPt_of tE htE hBs h1 h2 h3)

theorem valEx_of_rep' (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (h1 : EvRatRep emb embLL G A pos embV) (h2 : ChiRatAll S embLL) :
    ValEx S emb embLL G A pos embV yc :=
  valEx_of_rep tE htE hc hBs hA hP hO h1 h2 (vtupStab tE)

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.SpanImageEq
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

end Gen

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

abbrev FormsJ (j : ℕ) : Type := FormsLL (Fl.Pj j) (Lv.comp j) (c.embW u w h) (Lv.Int j)

variable {c Tw u w h Lv}


def DescUp (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) : Prop :=
  ∀ j, j + 1 ≤ D.R.m → MRatSpan (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (Lv.Int (j + 1))

end Formalism.L2.G.Cmp
end
end

