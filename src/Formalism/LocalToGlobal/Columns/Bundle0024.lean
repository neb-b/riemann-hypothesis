module

public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.LocalToGlobal.Columns.Bundle0023
public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0018
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.Bundle0001
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ExistsPlaceOverFirstPrime
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Repack0

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {sp : Spaces R F E} {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
  {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {bad : Set (HeightOneSpectrum (𝓞 F))}

def LevPack.toCol (P : LevPack sp.cm R.k sp.gram0 gp A.T R.f bad (C.stab 0) fun c => sp.crdLat0 (clsLat 0 c))
    (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (spl_sig : ∀ i v h x, spl i v h (sigR sp.cm.sig (v.adicCompletion F) x) = swapR _ (spl i v h x))
    (hiw : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), x ∈ P.lev.Uloc v ↔
        (1 : GL (Fin R.k) (v.adicCompletion F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU F R.k v)
    (w1 : HeightOneSpectrum (𝓞 F)) (reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal) :
    ColLevel R F E sp gp C A clsLat where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := P.lev.Lb_int
  Lb_dual := P.lev.Lb_dual
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_le := P.lev.Uloc_le
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  splitG := spl
  splitG_sig := spl_sig
  frG := fun _ _ _ => 1
  Uloc_g := hiw
  fM := P.lev.fM
  fT := P.lev.fT
  fT_ne := P.lev.fT_ne
  fT_T := P.lev.fT_T
  fM_card := P.lev.fM_card
  fT_L := P.lev.fT_L
  UlocAlt := P.lev.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq
  U_compact := P.lev.U_compact
  U_open := P.lev.U_open
  w1 := w1
  reflection_mem_Glev_castSucc := reflection_mem_Glev_castSucc
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := P.cls.stabI_range
  stabI_lat := P.cls.stabI_lat

end Repack0

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
      X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F)

def IwLoc : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
    ∀ x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (v.adicCompletion X.F), x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
      (1 : GL (Fin n) (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F n v

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

theorem levPack_iw (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (hI : IwLoc hc u Λ spl) (H : HCrd Pr n fun c => (s c).1.L) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
      ∀ x ∈ UPts hc.sig H.J (v.adicCompletion X.F), x ∈ (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc v ↔
        (1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F H.n' v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact hI

def th_resMap (P : Pl X.E) : 𝓞 X.F ⧸ (underPl X.F P).asIdeal →+* 𝓞 X.E ⧸ P.asIdeal :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E)) (le_of_eq rfl)

include hPr in
theorem th_resMap_bij (P : {P // P ∈ Pr.vT u}) : Function.Bijective (th_resMap (X := X) P.1) := by
  constructor
  · exact Ideal.quotientMap_injective' (le_of_eq rfl)
  · intro b
    haveI : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    haveI : Nontrivial (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.1.isPrime.ne_top
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← Ideal.absNorm_eq_natCard]
      exact hPr.vT_norm u P.1 P.2
    obtain ⟨k, hk⟩ := mem_zmultiples_of_prime_card hcard (g := (1 : 𝓞 X.E ⧸ P.1.asIdeal)) (g' := b) one_ne_zero
    refine ⟨(k : 𝓞 X.F ⧸ (underPl X.F P.1).asIdeal), ?_⟩
    rw [map_intCast, ← hk]
    simp

def tieFv (P : {P // P ∈ Pr.vT u}) : (𝓞 X.E ⧸ P.1.asIdeal) ≃+* (𝓞 X.F ⧸ (tieEV hc hX hPr u P).1.asIdeal) :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm

theorem tieFv_mk (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    tieFv hc hX hPr u P (Ideal.Quotient.mk P.1.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) x)) = Ideal.Quotient.mk _ x :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm_apply_apply (Ideal.Quotient.mk _ x)


include hX hPr in
theorem exists_place_over_first_prime : ∃ v : HeightOneSpectrum (𝓞 X.F), (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal := by
  have hcard : 0 < (Pr.vG 0).card := by rw [hPr.vG_card 0]; exact hX.f_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.1 hcard
  refine ⟨underPl X.F P, ?_⟩
  show (Pr.g 0 : 𝓞 X.F) ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast, ← hPr.piG_norm 0]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs hP)

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MaxSlopeSummandOfFock
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex E] [_root_.NumberField.IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValRat
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct Pointwise

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Pol

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

theorem smul_mem_RatSpanG (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : s r • p ∈ RatSpanG s lam := by
  unfold RatSpanG at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatSpanG_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatSpanG s (fun τ => shW (lam τ) (c τ)) = RatSpanG s lam := by
  unfold RatSpanG
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatSpanG (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatSpanG at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatSpanG (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatSpanG s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatSpanG s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatSpanG s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatSpanG s lam c hx

theorem mem_RatSpanG_iff (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    p ∈ RatSpanG s lam ↔ ∃ F ∈ VV K lam, MvPolynomial.map s F = p :=
  ⟨exists_VV_of_mem_RatSpanG s lam, by rintro ⟨F, hF, rfl⟩; exact map_mem_RatSpanG s lam hF⟩

end Pol

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)


end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQCmp
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section Cmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)

include hint hPv in
theorem qsp_val_one (t : 𝓞 E) (ht : t ∉ P.asIdeal) : Valued.v (φ (algebraMap (𝓞 E) E t)) = 1 :=
  le_antisymm (hint t) (not_lt.1 fun h => ht ((hPv t).1 h))

theorem qsp_frac (x : E) (hx : P.valuation E x ≤ 1) :
    ∃ (a : 𝓞 E) (t : 𝓞 E), t ∉ P.asIdeal ∧ x * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hnd
  have hd0 : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspan : Ideal.span {(d : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hd0
  have hPu : ¬ IsUnit P.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact P.isPrime.ne_top
  obtain ⟨e, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPu
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  have hvd : P.intValuation (d : 𝓞 E) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [P.intValuation_le_pow_iff_dvd, hJ]
    exact dvd_mul_right _ _
  have hvn : P.intValuation n ≤ WithZero.exp (-(e : ℤ)) := by
    refine le_trans ?_ hvd
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) ≤ P.valuation E (algebraMap (𝓞 E) E (d : 𝓞 E))
    rw [← hnd, map_mul]
    exact mul_le_of_le_one_left' hx
  have hnt : n * t ∈ Ideal.span {(d : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ((P.intValuation_le_pow_iff_mem n e).1 hvn) htJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hnt
  refine ⟨a, t, htP, ?_⟩
  have hD : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd0
  have hat : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d =
      algebraMap (𝓞 E) E n * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, ha]
  apply mul_right_cancel₀ hD
  linear_combination (algebraMap (𝓞 E) E t) * hnd - hat


include hint hPv in
theorem qsp_le_of_val (x : E) (hx : P.valuation E x ≤ 1) : Valued.v (φ x) ≤ 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx
  have h1 := qsp_val_one P φ hint hPv t ht
  have h2 := hint a
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2


include hint hPv in
theorem qsp_lt_of_val (x : E) (hx : P.valuation E x < 1) : Valued.v (φ x) < 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx.le
  have h1 := qsp_val_one P φ hint hPv t ht
  have ha : a ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← hxt, map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 ht, mul_one]
    exact hx
  have h2 := (hPv a).2 ha
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2


include hint hPv in
theorem qsp_val_iff (x : E) : Valued.v (φ x) ≤ 1 ↔ P.valuation E x ≤ 1 := by
  refine ⟨fun h => ?_, qsp_le_of_val P φ hint hPv x⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hinv : P.valuation E x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).1 hc
  have hlt := qsp_lt_of_val P φ hint hPv x⁻¹ hinv
  rw [map_inv₀] at hlt
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx0
  exact absurd h (not_le.2 ((Valuation.one_lt_val_iff _ hφ).2 hlt))


include hint hPv in
theorem qsp_mod (x d : E) (hd : d ≠ 0) (z : v.adicCompletion F) (hz : Valued.v z ≤ 1) (hxz : φ x = φ d * z) :
    P.valuation E x ≤ P.valuation E d := by
  have hφd : φ d ≠ 0 := (map_ne_zero φ).2 hd
  have h1 : φ (x / d) = z := by
    rw [map_div₀, hxz, mul_div_cancel_left₀ _ hφd]
  have h2 : P.valuation E (x / d) ≤ 1 := (qsp_val_iff P φ hint hPv _).1 (by rw [h1]; exact hz)
  have h3 : x = x / d * d := by rw [div_mul_cancel₀ _ hd]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' h2

end Cmp

end Formalism.L2.Col
end
end

