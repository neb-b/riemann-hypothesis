module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ZLat

open GlobalTheory.SW.TensLat GlobalTheory.SW.TensVac

theorem exists_even_reps {G : Type} [AddCommGroup G] (A C : AddSubgroup G) {M : ℕ} (hM : Odd M)
    (hA : ∀ a ∈ A, M • a ∈ C) {c : ℕ} (hc : C.relIndex A = c) (h0 : c ≠ 0) :
    ∃ a : Fin c → G, (∀ i, a i ∈ A) ∧ (∀ i i', 2 • a i - 2 • a i' ∈ C → i = i') ∧
      ∀ y ∈ A, ∃ i, y - 2 • a i ∈ C := by
  obtain ⟨k, rfl⟩ := hM
  have hcard : Nat.card (A ⧸ C.addSubgroupOf A) = c := hc
  haveI : Finite (A ⧸ C.addSubgroupOf A) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  let e := (Finite.equivFinOfCardEq hcard).symm
  have key (x : A) : 2 • ((k + 1) • (x : G)) = x + (2 * k + 1) • (x : G) := by
    rw [smul_smul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, succ_nsmul, add_comm]
  refine ⟨fun i => (k + 1) • ((e i).out : A), fun i => A.nsmul_mem (e i).out.2 _, ?_, ?_⟩
  · intro i i' h
    apply e.injective
    rw [← QuotientAddGroup.out_eq' (e i), ← QuotientAddGroup.out_eq' (e i'), eq_comm,
      QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [key, key] at h
    have := C.add_mem (C.sub_mem h (hA _ (e i).out.2)) (hA _ (e i').out.2)
    convert this using 1
    push_cast
    abel
  · intro y hy
    refine ⟨e.symm (⟨y, hy⟩ : A), ?_⟩
    rw [key, Equiv.apply_symm_apply]
    have h := QuotientAddGroup.out_eq' ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have := C.sub_mem h (hA _ ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A).out.2)
    convert this using 1
    push_cast
    abel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

omit [IsCMField E] in
theorem stdLat_eq : stdLat E n = stdL E n := by
  ext x
  rw [Base.mem_stdL, stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [IsCMField E] in
theorem mem_span_smul {N : ℕ} {S : Lt E n} {v : Fin n → E} :
    v ∈ Ideal.span {(N : 𝓞 E)} • S ↔ ∃ v' ∈ S, N • v' = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Nat.cast_smul_eq_nsmul]

omit [IsCMField E] in
theorem vecMulVec_nsmul (N : ℕ) (v : Fin n → E) (u : Fin r → E) :
    vecMulVec (N • v) u = N • vecMulVec v u := by
  ext i j
  simp [vecMulVec_apply, _root_.mul_assoc]

omit [IsCMField E] in
theorem mem_tens_span_smul {N : ℕ} {S : Lt E n} {L : Lt E r} {y : Matrix (Fin n) (Fin r) E} :
    y ∈ tens (Ideal.span {(N : 𝓞 E)} • S) L ↔ ∃ z ∈ tens S L, N • z = y := by
  have : tens (Ideal.span {(N : 𝓞 E)} • S) L = (tens S L).map (nsmulAddMonoidHom N) := by
    apply le_antisymm
    · refine tens_le fun v hv u hu => ?_
      obtain ⟨v', hv', rfl⟩ := mem_span_smul.1 hv
      exact ⟨_, pure_mem hv' hu, (vecMulVec_nsmul N v' u).symm⟩
    · rw [AddSubgroup.map_le_iff_le_comap]
      refine tens_le fun v hv u hu => ?_
      rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
      exact pure_mem (mem_span_smul.2 ⟨v, hv, rfl⟩) hu
  rw [this]
  rfl

theorem nsmul_mem_std {N : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n 1)
    (h : Ideal.span {(N : 𝓞 E)} • stdL E n ≤ Λ) {v : Fin n → E} (hv : v ∈ Λ) :
    N • v ∈ stdL E n := by
  rw [(Base.stdL_mem_Vset (E := E) n 1).2.1]
  intro y hy
  have := (hΛ.2.1 v).1 hv _ (h (mem_span_smul.2 ⟨y, hy, rfl⟩))
  convert this using 1
  simp only [Base.herm_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cc]
  ring

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E}
  {A B C : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem sum_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) (hCA : C ≤ A) (hCB : C ≤ B) {c : ℕ} (u : Fin c → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, u i ∈ A) (h2 : ∀ i i', u i - u i' ∈ C → i = i') (h3 : ∀ y ∈ A, ∃ i, y - u i ∈ C)
    {v : TF n g} (hv : IsVac X bas w B v) :
    ∑ i, epsW X w (u i) • heisG X bas (u i) v = (c : ℂ) • projA X bas w A v := by
  obtain ⟨v', hv', -⟩ := hA.vac (bas := bas) hs
  have hsb (i) := rho_sb (w := w) idx hs hn (u i) hv.1
  have hsum (s : Finset (Fin c)) : IsSB (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) ∧
      SW.ip (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) v' = s.card * SW.ip v v' := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨isSB_zero, ?_⟩
      have := ip_smul_left 0 hv'.1 hv'.1
      simpa using this
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ip_add_left (hsb a) ih.1 hv'.1, ih.2, Finset.card_insert_of_notMem ha]
      refine ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ _ _ _ _ (hsb a) ih.1).1, ?_⟩
      have := rho_ip (w := w) idx hs hn (u a) hv.1 hv'.1
      rw [hv'.2.2 _ (h1 a)] at this
      rw [this]
      push_cast
      ring
  obtain ⟨k1, k2⟩ := hsum Finset.univ
  rw [hA.uniq hs hv' k1, k2, (hA.proj idx hs hn hv.1 hv').2, smul_smul, Finset.card_univ,
    Fintype.card_fin]
  intro y hy
  choose σ hσ using fun i => h3 (y + u i) (A.add_mem hy (h1 i))
  have hinj : Function.Injective σ := by
    intro i i' h
    apply h2
    have := C.sub_mem (hσ i) (hσ i')
    rw [h] at this
    convert this using 1
    abel
  have hlin (f : Fin c → SW.TF n g) : heisG X bas y (∑ i, f i) = ∑ i, heisG X bas y (f i) := by
    funext x; simp [heisG, heisS, Finset.sum_mul]
  rw [hlin, Finset.smul_sum]
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hA.rho_rho idx hs hn hy (h1 i) hv.1]
  conv_rhs => rw [← hv.2.2 _ (hCB (hσ i))]
  rw [hA.rho_rho idx hs hn (h1 _) (hCA (hσ i)) hv.1, add_sub_cancel]

end

theorem exists_reps_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ N hN hle
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hA : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hle' := hle
  rw [stdLat_eq] at hle'
  have hsp : Submodule.span E ((Ideal.span {(N : 𝓞 E)} • stdL E n : Lt E n) : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← DualFamily.span_eq_top _ hstd.1 fun x => (hstd.2.1 x).2, Submodule.span_le]
    intro x hx
    have : x = (N : E)⁻¹ • (N • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_span_smul.2 ⟨x, hx, rfl⟩))
  have hidx : (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L).relIndex (tens Λ L) =
      (⟨Λ⟩ : GenLat E n).zCard N r := by
    rw [relIndex_tens_left hL.1 (span_of_selfD X hL) hΛ.1 hsp, GenLat.zCard, stdLat_eq]
    rfl
  have hfin : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
    have hfg : Λ.toAddSubgroup.FG := by
      haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
    haveI : AddGroup.FG Λ.toAddSubgroup := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
    haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ.toAddSubgroup
      (mul_ne_zero hN0 hN0)
    have : (nsmulAddMonoidHom (α := Λ.toAddSubgroup) (N * N)).range ≤
        (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup := by
      rintro _ ⟨x, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, stdLat_eq, mem_span_smul]
      exact ⟨N • (x : Fin n → E), nsmul_mem_std hΛ hle' x.2, by simp [mul_smul]⟩
    exact (AddSubgroup.finiteIndex_of_le this).index_ne_zero
  have hz : 0 < (⟨Λ⟩ : GenLat E n).zCard N r := pow_pos (Nat.pos_of_ne_zero hfin) r
  have hm : 0 < (⟨Λ⟩ : GenLat E n).mIdx N r := by
    refine pow_pos (Nat.pos_of_ne_zero fun h => hfin ?_) r
    exact AddSubgroup.relIndex_eq_zero_of_le_right (K := (⟨Λ⟩ : GenLat E n).Ln.toAddSubgroup)
      (fun x hx => hx.1) h
  have hNA : ∀ y ∈ tens Λ L, N • y ∈ tens (stdL E n) L := by
    have : tens Λ L ≤ (tens (stdL E n) L).comap (nsmulAddMonoidHom N) :=
      tens_le fun v hv u hu => by
        rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
        exact pure_mem (nsmul_mem_std hΛ hle' hv) hu
    exact fun y hy => this hy
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_even_reps (tens Λ L)
    (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L) (hN.mul hN)
    (fun y hy => mem_tens_span_smul.2 ⟨_, hNA y hy, by rw [mul_smul]⟩) hidx hz.ne'
  refine ⟨fun i => 2 • a i, fun i => ⟨AddSubgroup.nsmul_mem _ (ha1 i) 2, fun b =>
    ⟨_, (mem_tens_stdL L _).1 (hNA _ (ha1 i)) b, ?_⟩⟩, fun i i' h => ha2 i i' ?_, hz, hm,
    fun v hv => ?_⟩
  · exact smul_comm N 2 (a i b)
  · choose z hz hz' using h
    refine mem_tens_span_smul.2 ⟨z, (mem_tens_stdL L _).2 hz, ?_⟩
    funext b
    exact (hz' b).symm
  · rw [← sum_reps idx hs hn hA (C := tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L)
      (tens_le fun v hv u hu => pure_mem (hle' hv) hu)
      (tens_le fun v hv u hu => pure_mem (Submodule.smul_le_right hv) hu)
      (fun i => 2 • a i) (fun i => AddSubgroup.nsmul_mem _ (ha1 i) 2) ha2 ha3 hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eps_two hs (ha1 i), one_smul]

end GlobalTheory.Dict.ZLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_lift_of_projective {R P V Q : Type} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup V] [Module R V] [Group Q] (act : R → Q → Q) (L : Submodule R V) (ev : P → Q) (φ : V → Q)
    (ev_add : ∀ a b, ev (a + b) = ev a * ev b) (ev_lin : ∀ (s : R) a, ev (s • a) = act s (ev a))
    (φ_add : ∀ a b, φ (a + b) = φ a * φ b) (φ_lin : ∀ (s : R) a, φ (s • a) = act s (φ a))
    (onto : ∀ a, ∃ v ∈ L, ev a = φ v) : ∃ mk : P →ₗ[R] V, ∀ a, mk a ∈ L ∧ ev a = φ (mk a) := by
  have hev0 : ev 0 = 1 := mul_left_cancel (a := ev 0) (by rw [_root_.mul_one, ← ev_add, add_zero])
  have hφ0 : φ 0 = 1 := mul_left_cancel (a := φ 0) (by rw [_root_.mul_one, ← φ_add, add_zero])

  let W : Submodule R (P × L) :=
    { carrier := {x | ev x.1 = φ (x.2 : V)}
      add_mem' := by
        rintro ⟨a, v⟩ ⟨b, w⟩ ha hb
        simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, Submodule.coe_add] at *
        rw [ev_add, φ_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero]
        rw [hev0, hφ0]
      smul_mem' := by
        rintro s ⟨a, v⟩ ha
        simp only [Set.mem_ofPred_eq, Prod.smul_mk, Submodule.coe_smul] at *
        rw [ev_lin, φ_lin, ha] }
  let f : W →ₗ[R] P := (LinearMap.fst R P L).comp W.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, he⟩ := onto a
    exact ⟨⟨(a, ⟨v, hv⟩), he⟩, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨L.subtype.comp ((LinearMap.snd R P L).comp (W.subtype.comp h)), fun a => ⟨((h a : W) : P × L).2.2, ?_⟩⟩
  have h1 : ((h a : W) : P × L).1 = a := LinearMap.congr_fun hh a
  have h2 : ev ((h a : W) : P × L).1 = φ (((h a : W) : P × L).2 : V) := (h a).2
  rw [h1] at h2
  exact h2

private theorem pv_add_siegel_theta_transformation {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (u v : Fin r → E) :
    pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  have hemb : ∀ τ : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (u + v) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := fun τ => by
    funext a
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  funext j
  simp only [pv, Function.comp_apply, Pi.add_apply, GlobalTheory.ThFr.per, hemb]
  split_ifs
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  · rw [Matrix.mulVec_add, Pi.add_apply]

theorem exists_mark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk ∧ A.Marked mk := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have := Dw.proj
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom ℂ y.x _ y.x_over

  obtain ⟨m, hm, c0, hc0, hmc⟩ : ∃ m ∈ l.Mb, ∃ c0 ∈ Mfr l, m + c0 = 1 := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMC : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hex0 : A.ex 0 = 1 := mul_left_cancel (a := A.ex 0) (by rw [_root_.mul_one, ← A.ex_add, add_zero])
  have hexn : ∀ (n : ℕ) z, A.ex (n • z) = A.ex z ^ n := by
    intro n z
    induction n with
    | zero => rw [zero_smul, hex0, pow_zero]
    | succ n ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  have hpvs : ∀ (a : E) (v : Fin r → E), pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
    fun a v => pv_smul idx x a v
  have hinj : Function.Injective (pv X idx x) := (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  have hsv : ∀ (s : 𝓞 E) (v : Fin r → E), s • v = (s : E) • v := fun _ _ => rfl

  let φ : (Fin r → E) → (ptO Xo y.x ⟶ Xo.univ.t.G) := fun v => A.ex (pv X idx x ((l.M : E)⁻¹ • v))
  have hφadd : ∀ u v, φ (u + v) = φ u * φ v := fun u v => by
    simp only [φ, smul_add, pv_add_siegel_theta_transformation, A.ex_add]
  have hφlin : ∀ (s : 𝓞 E) v, φ (s • v) = φ v ≫ Xo.univ.t.act.act s := fun s v => by
    simp only [φ]
    rw [← A.ex_lin, ← hpvs, hsv, smul_comm]

  have heta : ∀ a, Xo.univ.eta a = Xo.univ.eta (c0 • a) := by
    intro a
    have h1 : a = c0 • a + m • a := by rw [← add_smul, add_comm, hmc, one_smul]
    conv_lhs => rw [h1]
    rw [Xo.univ.eta_add, Xo.univ.eta_ker (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top),
      _root_.mul_one]
  have hlev : ∀ a, levPt Xo y.x a = I.ev l.M (c0 • a) := by
    intro a
    rw [levPt, heta a]
    exact hI _ (Submodule.smul_mem_smul hc0 Submodule.mem_top)
  obtain ⟨mk, hmk⟩ := exists_lift_of_projective (fun s q => q ≫ Xo.univ.t.act.act s) L
    (fun a => I.ev l.M (c0 • a)) φ (fun a b => by rw [smul_add, I.add])
    (fun s a => by rw [smul_comm c0 s a, I.lin]) hφadd hφlin (by
      intro a
      obtain ⟨z, hz⟩ := A.ex_onto (I.ev l.M (c0 • a))
      have hp : A.ex z ^ l.M = 1 := by
        rw [hz]
        exact (I.onto l.M hM0 _).mpr ⟨_, rfl⟩
      rw [← hexn] at hp
      obtain ⟨v, hv, hzv⟩ := (A.ex_ker _).mp hp
      refine ⟨v, hv, ?_⟩
      rw [← hz]
      show A.ex z = A.ex (pv X idx x ((l.M : E)⁻¹ • v))
      congr 1
      rw [hpvs, ← hzv]
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [inv_mul_cancel_left₀ hMC])

  have hevmk : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), I.ev l.M a = φ (mk a) := by
    intro a ha
    rw [← hI a ha, ← (hmk a).2]
    exact hlev a

  have hdiff : ∀ u v, φ u = φ v → ∃ w ∈ L, u - v = l.M • w := by
    intro u v huv
    have h1 : φ (u - v) = 1 := by
      have h2 := hφadd (u - v) v
      rw [sub_add_cancel, huv] at h2
      exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
    obtain ⟨w, hw, hw'⟩ := (A.ex_ker _).mp h1
    refine ⟨w, hw, ?_⟩
    have h3 := hinj hw'
    rw [← h3, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hME]

  have hML : ∀ v ∈ Mfr l • L, ∃ u ∈ L, m • v = l.M • u := by
    intro v hv
    have h1 : m • v ∈ (l.Mb * Mfr l) • L := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hm hv
    rw [Mfr, l.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨u, hu, by rw [← hu', Nat.cast_smul_eq_nsmul]⟩
  refine ⟨mk, ⟨fun a => (hmk a).1, ?_, ?_⟩, fun a _ => (hlev a).trans (hmk a).2⟩
  · intro a ha hau
    obtain ⟨u, hu, hau⟩ := hau
    apply (I.ker l.M hM0 a).mp
    rw [hevmk a ha]
    show A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)) = 1
    rw [hau, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hME]
    exact (A.ex_ker _).mpr ⟨u, hu, rfl⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.smul_le_right hv
    have hp : φ v ^ l.M = 1 := by
      have h1 : l.M • pv X idx x ((l.M : E)⁻¹ • v) = pv X idx x v := by
        rw [hpvs]
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
        rw [mul_inv_cancel_left₀ hMC]
      show A.ex (pv X idx x ((l.M : E)⁻¹ • v)) ^ l.M = 1
      rw [← hexn, h1]
      exact (A.ex_ker _).mpr ⟨v, hvL, rfl⟩
    obtain ⟨a0, ha0⟩ := (I.onto l.M hM0 (φ v)).mp hp
    have haM : c0 • a0 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hc0 Submodule.mem_top
    have h3 : φ (mk (c0 • a0)) = φ (c0 • v) := by
      rw [← hevmk _ haM, I.lin, ha0, hφlin]
    obtain ⟨w, hw, hw'⟩ := hdiff _ _ h3.symm
    obtain ⟨u', hu', hmv⟩ := hML v hv
    refine ⟨c0 • a0, haM, u' + w, L.add_mem hu' hw, ?_⟩
    calc v = m • v + c0 • v := by rw [← add_smul, hmc, one_smul]
      _ = mk (c0 • a0) + (l.M • u' + l.M • w) := by rw [hmv, ← hw']; abel
      _ = mk (c0 • a0) + l.M • (u' + w) := by rw [smul_add]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ProjProj

open GlobalTheory.SW.TensVac

theorem proj_proj_of_good {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A₁ A₂ A₃ : AddSubgroup (Matrix (Fin n) (Fin r) E)} (h₂ : Good X w A₂) (h₃ : Good X w A₃)
    (hle : A₂ ≤ (A₂ ⊓ A₁) ⊔ (A₂ ⊓ A₃)) {v : TF n g} (hv : IsVac X bas w A₁ v) :
    projA X bas w A₃ (projA X bas w A₂ v) = projA X bas w A₃ v := by
  obtain ⟨v₂, hv₂, -⟩ := h₂.vac hs
  obtain ⟨v₃, hv₃, -⟩ := h₃.vac hs
  have hsb₂ := (h₂.proj idx hs hn hv.1 hv₂).1
  rw [(h₃.proj idx hs hn hsb₂ hv₃).2, (h₃.proj idx hs hn hv.1 hv₃).2]
  congr 1
  have hfin := h₂.finite idx hs hn hv.1
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hv.1
  have hpos : (((fun y => epsW X w y • heisG X bas y v) '' A₂).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨_, 0, A₂.zero_mem, rfl⟩).ne'
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv₃.1
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv₃.1, h2,
    Finset.sum_congr rfl (g := fun _ => SW.ip v v₃), Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul, inv_mul_cancel_left₀ hpos]
  intro ψ hψ
  obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hψ
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
  show SW.ip (epsW X w (a + b) • heisG X bas (a + b) v) v₃ = SW.ip v v₃
  rw [add_comm a b, ← h₂.rho_rho idx hs hn hb.1 ha.1 hv.1, hv.2.2 a ha.2,
    ← rho_ip (w := w) idx hs hn b hv.1 hv₃.1, hv₃.2.2 b hb.2]

theorem proj_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ L₃ : Lt E r, SelfD X L₁ → SelfD X L₂ → SelfD X L₃ → ∀ Λ₁ ∈ Vset E n 1, ∀ Λ₂ ∈ Vset E n 1, ∀ Λ₃ ∈ Vset E n 1, tens Λ₂ L₂ ≤ (tens Λ₂ L₂ ⊓ tens Λ₁ L₁) ⊔ (tens Λ₂ L₂ ⊓ tens Λ₃ L₃) → ∀ v : TF n g, IsVac X bas w (tens Λ₁ L₁) v → projA X bas w (tens Λ₃ L₃) (projA X bas w (tens Λ₂ L₂) v) = projA X bas w (tens Λ₃ L₃) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L₁ L₂ L₃ _ hL₂ hL₃ Λ₁ _ Λ₂ hΛ₂ Λ₃ hΛ₃ hle v hv
  have good (L) (hL : SelfD X L) (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  exact proj_proj_of_good idx hs hn (good L₂ hL₂ Λ₂ hΛ₂) (good L₃ hL₃ Λ₃ hΛ₃) hle hv

end GlobalTheory.Dict.ProjProj
end

