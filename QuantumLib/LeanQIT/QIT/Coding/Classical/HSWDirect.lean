/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSWDirect.TensorPower
public import QIT.Coding.Classical.HSWDirect.Rates
public import QIT.Coding.Classical.HSWDirect.CodeTransforms
public import QIT.Coding.Classical.HSWDirect.WitnessAssembly
public import QIT.Coding.Classical.HSWDirect.RegularizedAssembly

/-!
# HSW direct-achievability bridge

This module sits after the HSW packing and conditional-typicality layers.  It
does not prove new typicality estimates; it packages a completed
`HSWPackingHypothesesSpectral` bundle into the average-error coding witness
used by the operational direct-achievability assembly.

The full HSW direct theorem still requires a source-shaped family of these
witnesses for every block-channel ensemble, including the message-size and
packing-error asymptotics.  This module proves the downstream operational
assembly and the block-channel rate-normalization transport.
[Wilde2011Qst, qit-notes.tex:33634-33808]
-/
