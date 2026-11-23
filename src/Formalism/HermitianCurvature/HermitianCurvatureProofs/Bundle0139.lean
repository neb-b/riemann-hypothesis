module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFnM : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rvhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rvhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem rim_herm (v w : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg 1 (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) := by
  have e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) =
      fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c := by
    funext g
    simp only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]
  rw [e]
  exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _
    (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))

theorem rim_rowV (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (p q : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => rowV k r z g J p q) := by
  unfold rowV
  by_cases h : p.val < r
  · simp only [dif_pos h]
    exact rim_herm _ _
  · by_cases h2 : p.val = r
    · simp only [dif_neg h, dif_pos h2]
      exact rim_herm _ _
    · simp only [dif_neg h, dif_neg h2]
      exact pd_const _ 1

theorem rim_alJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => alJ k r z g J) :=
  pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by
    simpa only [Matrix.of_apply] using rim_rowV z J a b

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rimCat {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) : List ι → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ rimCat Θs l

theorem rimCat_poly {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (rimCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)

theorem rimCat_apply {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (rimCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [rimCat, B.opApply]
  | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]

theorem rimCat_order {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : ι) (l : List ι) :
    B.opOrder (rimCat Θs (i :: l)) = t := by
  rw [rimCat, QMinOp.opOrder_append, ho i]
  exact max_eq_left (ri_order_le _ (rimCat_poly h l))

theorem residue_rows_strict_mono : StrictMono (rowsR k r 0) := by
  intro a b h
  have h' : a.val < b.val := h
  show (rowsR k r 0 a).val < (rowsR k r 0 b).val
  simp only [rowsR]
  split_ifs <;> omega

theorem rim_mem : rowsR k r 0 ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (residue_rows_strict_mono (k := k) (r := r))

theorem rim_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rvhatOp k r z z' Y F g := by
  have h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)),
      ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ j ∈ ({()} : Finset Unit),
          (fun (_ : Unit) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (x.1 : ℕ)) * z' (wI k r x.1) * alJ k r z g x.2)) j g •
            qminorOp (Q.EH k r) x.2 ((fun (_ : Unit) => colsV k r x.1) j) (Q.uC k r (Fin.last r) Y - 1) F g := fun x =>
    QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _
      (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _
  choose Θs hP hO hR using h
  let idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1))) :=
    ((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList
  have hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx := by
    simp only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]
    exact rim_mem
  refine ⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩
  · obtain ⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by
      cases h' : idx with
      | nil => rw [h'] at hmem; exact absurd hmem List.not_mem_nil
      | cons i l => exact ⟨i, l, rfl⟩
    rw [hl]
    exact rimCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [rimCat_apply]
    simp only [idx]
    rw [Finset.sum_map_toList, Finset.sum_product]
    simp only [rvhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]

end ops

theorem jDRRealInvM_of_inv (hI : JDRInvFnM) : JDRRealInvM := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

section

variable {k r : ℕ}

theorem unipotent_fixes_anisotropic_vector (l : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) : Q.w1 k r l c *ᵥ v = v := by
  have hsum : v = ∑ q, v q • bvec q := by
    funext p
    simp [bvec, Finset.sum_apply, Pi.single_apply]
  rw [hsum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases h1 : q = eI k r l
  · have : v q = 0 := hv q (Or.inl (by rw [h1]; simp [eI]))
    rw [this, zero_smul, zero_smul]
  by_cases h2 : q = esI k r l
  · have : v q = 0 := hv q (Or.inr (by rw [h2]; simp [esI]; omega))
    rw [this, zero_smul, zero_smul]
  rw [Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector l c h1 h2]

theorem top_wlist_wb (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    (L.map fun a => Q.w1 k r a (c a)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_anisotropic_vector a _ v hv]

theorem inv_wCell_last_mul_mulVec_of_inWb {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hgu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul hgu
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (g⁻¹ *ᵥ z) = z := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z g, Matrix.mul_nonsing_inv _ hgu, Matrix.one_mulVec]
    exact top_wlist_wb c _ z hz
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem top_qminor_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n t t' : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = t') (a b : Fin t' → Fin n) (u : ℂ) :
    qminorOp Eop (a ∘ Fin.cast h) (b ∘ Fin.cast h) u = qminorOp Eop a b u := by
  subst h
  rfl

theorem top_chatL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℕ} (h : t = k + 1)
    (pos : Fin t → Fin (2 * r + k + 1)) (hpos : ∀ j, (pos j).val = r + j.val) (u : ℂ)
    (a β : Q.Mx k r → Fin t → ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Q.chatL (Q.EH k r) pos u a β f g = ∑ s : Fin (k + 1), ∑ t' : Fin (k + 1),
      (((-1 : ℂ) ^ ((s : ℕ) + (t' : ℕ))) * β g (Fin.cast h.symm s) * a g (Fin.cast h.symm t')) •
        qminorOp (Q.EH k r) (rowsN k r (Fin.last r) s) (rowsN k r (Fin.last r) t') u f g := by
  subst h
  unfold Q.chatL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t' _ => ?_
  have hc : k + 1 - 1 = r - (Fin.last r).val + k := by simp
  have e : ∀ i : Fin (k + 1), pos ∘ Q.skip1 i = rowsN k r (Fin.last r) i ∘ Fin.cast hc := by
    intro i
    funext j
    apply Fin.ext
    simp only [Function.comp_apply, Q.skip1, rowsN, Fin.val_last, Fin.val_cast]
    split_ifs <;> simp_all <;> omega
  rw [e s, e t', top_qminor_cast]
  rfl

end

theorem residue_top_holds : JDRTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  simp only [FN, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, inv_wCell_last_mul_mulVec_of_inWb hc hg hz]
  congr 2
  · congr 1
    simp only [Q.xbv, fvec]
    congr 1
    · congr 1; apply Fin.ext; simp [Q.posL, wI]; omega
    · simp
  · simp only [Q.yv, fvec]
    congr 2
    · simp
    · apply Fin.ext; simp [Q.posL, wI]; omega

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ImageProdLoc
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormTwoSidedTranslateGrowthBound
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem norm_two_sided_translate_growth_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖e0 (x⁻¹ * A * y)‖ₑ ≤ ENNReal.ofReal (|C0| * (B.gN x * B.gN y) ^ b) * ‖B.gN A ^ (-b)‖ₑ := by
  have hxi := (MatrixMultiplicationContinuity.uh_inv hx).1
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hxi hA) hy
  have h1 : 1 ≤ B.gN (x⁻¹ * A * y) := ((hNI k r).2 _ hM).2
  have hAp : 0 ≤ B.gN A ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hxy : 0 ≤ (B.gN x * B.gN y) ^ b := Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  rw [Real.enorm_eq_ofReal hAp, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hxy), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖e0 (x⁻¹ * A * y)‖ ≤ C0 * B.gN (x⁻¹ * A * y) ^ (-a) := hb0e _ hM
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ |C0| * ((B.gN x * B.gN y) ^ b * B.gN A ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_sandwich hNI hx hA hy hb0) (abs_nonneg _)
    _ = |C0| * (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by ring

theorem lam_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hq : ∀ᵐ q ∂μq, Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    abelian₂ e0 γ μp μq x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-b)‖ₑ ∂μq ∂μp := by
  unfold abelian₂
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hq] with q hqq
  have hQi := (MatrixMultiplicationContinuity.uh_inv hqq).1
  have hA : (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hpp hγ) hQi
  have e : (Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
      Matrix.of y = (Matrix.of x)⁻¹ * ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) *
      Matrix.of y := by simp only [Matrix.mul_assoc]
  rw [e]
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hA hy

theorem lambda_integral_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Lam1 e0 μp x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)‖ₑ ∂μp := by
  unfold Lam1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hpp hy

end Formalism.FourierDecayAlt.P.S3dx4
end
end

