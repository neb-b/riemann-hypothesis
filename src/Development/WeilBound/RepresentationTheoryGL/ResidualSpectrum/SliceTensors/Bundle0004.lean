module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreA
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Abstract

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem idem_map {π : Representation ℂ G V} {π' : Representation ℂ G W} (hπ : IsSmooth π) (hπ' : IsSmooth π')
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (π g v) = π' g (f v)) (v : V) :
    f (idem hπ hH v) = idem hπ' hH (f v) := by
  have hy : f (idem hπ hH v) ∈ fixed π' H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← hf, GlobalTheory.LGrp.mem_fixed.1 (idem_mem hπ hH v) k hk]
  have hk : v - idem hπ hH v ∈ twKer π H 1 := (idem_eq_zero_iff hπ hH).1 (by
    rw [map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self])
  have hle : twKer π H 1 ≤ (twKer π' H 1).comap f := Submodule.span_le.2 (by
    rintro _ ⟨u, z, rfl⟩
    exact Submodule.subset_span ⟨u, f z, by rw [map_sub, map_smul, hf]⟩)
  have h0 : idem hπ' hH (f (v - idem hπ hH v)) = 0 := (idem_eq_zero_iff hπ' hH).2 (hle hk)
  rw [map_sub, map_sub, idem_of_mem hπ' hH hy, sub_eq_zero] at h0
  exact h0.symm

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {U : ∀ a, Subgroup (Γ a)}

theorem idem_tprod (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCompact (U a : Set (Γ a)))
    (hC : IsCompact (Subgroup.pi Set.univ U : Set (∀ a, Γ a))) (x : ∀ a, X a) :
    idem (isSmooth_piTensor hs) hC (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun a => idem (hs a) (hc a) (x a) := by
  classical
  have hS := isSmooth_piTensor hs
  have h1 : ∀ (x : ∀ a, X a) (i : α) (y : X i),
      idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i (idem (hs i) (hc i) y))) =
        idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i y)) := fun x i y => by
    let l : X i →ₗ[ℂ] ⨂[ℂ] a, X a := idem hS hC ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
    have hk : twKer (ρ i) (U i) 1 ≤ LinearMap.ker l := Submodule.span_le.2 (by
      rintro _ ⟨u, z, rfl⟩
      show l _ = 0
      rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
      have hu : Pi.mulSingle i (u : Γ i) ∈ Subgroup.pi Set.univ U := fun a _ => by
        show (Pi.mulSingle i (u : Γ i) : ∀ a, Γ a) a ∈ U a
        by_cases e : a = i
        · subst e; simp
        · rw [Pi.mulSingle_eq_of_ne e]; exact one_mem _
      refine Eq.trans ?_ (idem_apply_mem hS hC hu (PiTensorProduct.tprod ℂ (Function.update x i z)))
      rw [piTensor_tprod]
      show idem hS hC (PiTensorProduct.tprod ℂ _) = _
      congr 2
      funext a
      by_cases e : a = i
      · subst e; simp
      · simp [e])
    have h2 : l (idem (hs i) (hc i) y - y) = 0 := hk ((idem_eq_zero_iff (hs i) (hc i)).1 (by
      rw [map_sub, idem_of_mem _ _ (idem_mem _ _ _), sub_self]))
    rwa [map_sub, sub_eq_zero] at h2
  have h2 : ∀ (x : ∀ a, X a) (s : Finset α),
      idem hS hC (PiTensorProduct.tprod ℂ (s.piecewise (fun a => idem (hs a) (hc a) (x a)) x)) =
        idem hS hC (PiTensorProduct.tprod ℂ x) := fun x s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, h1, ← ih, ← Finset.piecewise_eq_of_notMem s (fun a => idem (hs a) (hc a) (x a)) x hi,
        Function.update_eq_self]
  rw [← h2 x Finset.univ, Finset.piecewise_univ, idem_of_mem]
  refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
  rw [piTensor_tprod]
  congr 1
  funext a
  exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem _ _ _) _ (hg a trivial)

end Abstract

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSatVecGL_twist {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (s : ℂ) {z : ℂˣ} (hz : (z : ℂ) = (qV E w : ℂ) ^ (-s)) :
    IsSatVecGL w (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) x (B.map (· * z)) := by
  have hfix : x ∈ fixed (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) (KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by
      rw [twist_apply, detChar_apply, absPow_det_of_mem s hg, Units.val_one, one_smul]
      exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g hg
  refine ⟨hx.1, hfix, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ n (Ov E w) ϖ j c.out = 0
  · simp [hc]
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hc
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det c.out =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change c.out.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
    simp
  have e3 : absPow (w.adicCompletion E) s (Units.mk0 ϖ hϖ0) = z := Units.ext (by
    have : ordV E w ϖ = 1 := by
      rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v ϖ = _ from hϖ]; rfl
    rw [val_absPow_completion, hz, Units.val_mk0, this]
    simp)
  rw [twist_apply, detChar_apply, e2, map_mul, map_mul, absPow_det_of_mem s ha, absPow_det_of_mem s hb, map_pow, e3,
    one_mul, mul_one, smul_comm, Units.val_pow_eq_pow_val]

variable {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)

theorem isSatVecGL_multiProd {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} (hs : ∀ a, IsSmooth (π a))
    {S : Fin c → Multiset ℂˣ} {x : ∀ a, X a} (hx : ∀ a, IsSatVecGL w (π a) (x a) (S a))
    {f : IndSp (stdBlocks N h) (piTensor π)} (hf : f ∈ fixed (multiProd (stdBlocks N h) π) (KGL w (n := n))) (h0 : f ≠ 0)
    {r : ℂ} (hr : f.1.1 1 = r • PiTensorProduct.tprod ℂ x) :
    IsSatVecGL w (multiProd (stdBlocks N h) π) f (∑ a, S a) := by
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hf' := hf
  rw [hKO] at hf'
  choose Z iZ mZ R β l y hR hβ hyS h1 hl using fun a => exists_model (w := w) (hx a).2.2.1
  have hy : ∀ a, y a ∈ fixed (R a) (KO _ _) := fun a => hKO _ ▸ (hyS a).2.1
  obtain ⟨F, hF, hF1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor R) (x := PiTensorProduct.tprod ℂ y)
    fun g hg => by
      rw [piTensor_tprod]
      congr 1
      exact funext fun a => GlobalTheory.LGrp.mem_fixed.1 (hy a) _ (hg a)
  obtain ⟨Y, hYe, hY⟩ := exists_map_isSatVecGL h h1 hl hF hF1
  rw [funext hβ] at hY
  refine ⟨h0, hf, hY.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hϖ0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  have hT := Tj_mem_hecke (n := n) hϖ j
  have hK : IsCommensurated (KGL w (n := n)) := Final.GLintComm E w n
  have e1 := (map_heckeVec (ρ := multiProd (stdBlocks N h) R) hK hT Y hYe F).trans (hY.2.2.2 ϖ hϖ j hj)
  rw [hKO] at hT hK e1 ⊢
  have hp : ∀ q : GL (Fin n) (w.adicCompletion E) ⧸ KO (w.adicCompletion E) (Fin n),
      ∃ p : parab (w.adicCompletion E) (stdBlocks N h), ((p : GL (Fin n) (w.adicCompletion E)) : _ ⧸ KO _ _) = q :=
    fun q => by
      obtain ⟨p, hp, u, hu, e⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 q.out
      exact ⟨⟨p, hp⟩, (QuotientGroup.eq.2 (by simpa [e] using hu)).trans q.out_eq'⟩
  choose p hp using hp
  have hω : ∀ q a, ∃ t : ℂ, Tj ℂ n (Ov E w) ϖ j (p q) ≠ 0 →
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj _ _ (p q) a) (x a)) = t • x a ∧
      idem (hR a) GlobalTheory.SplitFlip.isCompact_KO (R a (leviProj _ _ (p q) a) (y a)) = t • y a := fun q a => by
    by_cases hq : Tj ℂ n (Ov E w) ϖ j (p q) = 0
    · exact ⟨0, fun e => absurd hq e⟩
    obtain ⟨i1, i2⟩ := intM_of_Tj hϖ0 hϖ hq
    obtain ⟨l, hl, e⟩ := dosetInd_eq_Tj hϖ0 hϖ (g := leviProj _ _ (p q) a) (fun s t => i1 _ _) fun s t => by
      have := i2 (stdBlocks N h ⟨a, s⟩) (stdBlocks N h ⟨a, t⟩)
      rw [← Pi.inv_apply, ← map_inv]
      rw [Units.val_mul, tor_val, Matrix.diagonal_mul] at this ⊢
      exact this
    exact ⟨_, fun _ => ⟨idem_of_isSatVecGL (hs a) (hx a) hϖ hl e, idem_of_isSatVecGL (hR a) (hyS a) hϖ hl e⟩⟩
  choose ω hω using hω
  rw [heckeVec_multiProd _ hK hT hR hF (hF1.trans (one_smul ℂ _).symm) p hp ω (fun q hq a => (hω q a hq).2),
    map_smul] at e1
  rw [heckeVec_multiProd _ hK hT hs hf' hr p hp ω (fun q hq a => (hω q a hq).1), smul_left_injective ℂ hY.1 e1]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreC
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Corner

variable {R S : Type} [CommRing R] [CommRing S]

theorem cc_cornerGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S)
    (l : ∀ i, GL (Fin (n i)) R) :
    cornerGL N s (leviEmb R (stdBlocks n h) l) = leviEmb S (stdBlocks n h) (fun i => cornerGL (n i) s (l i)) := by
  have leviEmb_apply_same (T : Type) [CommRing T] (g : ∀ i, GL (Fin (n i)) T)
      (a : Fin c) (i j : Fin (n a)) :
      (leviEmb T (stdBlocks n h) g : Matrix (Fin N) (Fin N) T)
        (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨a, j⟩) = (g a : Matrix _ _ T) i j := by
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  have leviEmb_apply_ne (T : Type) [CommRing T] (g : ∀ i, GL (Fin (n i)) T)
      {a b : Fin c} (hab : a ≠ b) (i : Fin (n a)) (j : Fin (n b)) :
      (leviEmb T (stdBlocks n h) g : Matrix (Fin N) (Fin N) T)
        (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = 0 := by
    classical
    simp [leviEmb]
    letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, GlobalTheory.IwasawaAdelic.cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hij,
        leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ hab, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ hab, map_zero]

theorem cc_cornerGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R (stdBlocks n h)) : cornerGL N s u ∈ unipRad S (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

end Corner

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem iwasawa_inf {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GL (Fin (n i)) (Cinf E)) (k : Kinf E N),
      x = u * leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (m i)) *
        (infGL E N (Unitary.toUnits k) * finGL E N (Matrix.GeneralLinearGroup.map (pFin E) x)) := by
  obtain ⟨b, hb, k, hy⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  have hbP := GlobalTheory.IwasawaAdelic.mem_parab_of_upper n h b hb
  have hLmem (g : ∀ i, GL (Fin (n i)) (Cinf E)) :
      leviEmb (Cinf E) (stdBlocks n h) g ∈ parab (Cinf E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    classical
    simp [leviEmb]
    letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
    exact Matrix.blockDiagonal'_apply_ne _ _ _ (ne_of_gt hab)
  have hproj (g : ∀ i, GL (Fin (n i)) (Cinf E)) :
      leviProj (Cinf E) (stdBlocks n h) ⟨leviEmb (Cinf E) (stdBlocks n h) g, hLmem g⟩ = g := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hdec : ∃ u ∈ unipRad (Cinf E) (stdBlocks n h),
      b = leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) * u := by
    let L : parab (Cinf E) (stdBlocks n h) :=
      ⟨leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩),
        hLmem _⟩
    refine ⟨((L⁻¹ * ⟨b, hbP⟩ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)), ?_, ?_⟩
    · change ((L⁻¹ * ⟨b, hbP⟩ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)) ∈ _
      apply (coe_mem_unipRad (Cinf E) _).2
      change leviProj (Cinf E) (stdBlocks n h) (L⁻¹ * ⟨b, hbP⟩) = 1
      rw [map_mul, map_inv, hproj, inv_mul_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mul_inv_cancel_left _ _).symm
  obtain ⟨u, hu, hbu⟩ := hdec
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) with hL
  have hN := parab_le_normalizer (Cinf E) (stdBlocks n h) (hLmem (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩))
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  refine ⟨infGL E N (L * u * L⁻¹), GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h _ hu',
    fun i => leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩ i, k, ?_⟩
  rw [← GlobalTheory.IwasawaAdelic.infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  rw [hbu]
  simp only [map_mul, map_inv]
  group

theorem finGL_locGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ)) =
      leviEmb (Ad E) (stdBlocks n h) (fun i => finGL E (n i) (locGL E (n i) w (μ i))) := by
  rw [locGL, cc_cornerGL_leviEmb, finGL, cc_cornerGL_leviEmb]
  rfl

theorem finGL_locGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    finGL E N (locGL E N w u) ∈ unipRad (Ad E) (stdBlocks n h) := by
  exact cc_cornerGL_mem_unipRad n h _ (cc_cornerGL_mem_unipRad n h _ hu)

theorem commute_finGL_locGL {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {y : GA E N}
    (hy : Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y) = 1)
    (g : GL (Fin N) (w.adicCompletion E)) :
    y * finGL E N (locGL E N w g) = finGL E N (locGL E N w g) * y := by
  have hc := LocSph.comm_locGL w _ hy g
  conv_lhs => rw [← infGL_mul_finGL y]
  conv_rhs => rw [← infGL_mul_finGL y]
  rw [mul_assoc, ← (finGL E N).map_mul, hc, (finGL E N).map_mul, ← mul_assoc, infGL_comm, mul_assoc]

theorem exists_split_at {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (y : GA E N) :
    ∃ (y₀ : GA E N) (g : GL (Fin N) (w.adicCompletion E)),
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 ∧
        y = y₀ * finGL E N (locGL E N w g) := by
  set g := Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y)
  refine ⟨y * (finGL E N (locGL E N w g))⁻¹, g, ?_, by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, pFin_finGL, pLoc_locGL, mul_inv_cancel]

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

