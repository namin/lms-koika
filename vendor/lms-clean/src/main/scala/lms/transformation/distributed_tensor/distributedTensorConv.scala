package lms.transformation.tensor

import scala.annotation.implicitNotFound
import scala.collection._

import lms.core._
import lms.core.stub._
import lms.collection.mutable._
import lms.macros.SourceContext
import lms.thirdparty.array_computation.{ArrayCPUOps, CUDATypeLess, CudaOps}
import lms.thirdparty.{CUDNNTypeLess, CUDNNOps}
import lms.transformation.util.CudnnUtils

import Backend._

trait FixedSizeDistributedTensorConvTypeLess extends FixedSizeDistributedTensorMutationTypeLess with CudnnUtils {
  import BaseTypeLess._

  def ConvForward(input: TENSOR, filter: TENSOR, params: ConvParam, anno: Anno, __pos: SourceContext): TENSOR = {
    val res_tt = ConvForwardOutTensorType(input, filter, params)
    (new TENSOR(Adapter.g.reflectRead("tensor_conv", C(res_tt), C(anno),
      input.x, filter.x, C(params))(input.x, filter.x))).withSrcType(__pos, input.et)
  }

  def ConvBackwardData(input: TENSOR, filter: TENSOR, doutput: TENSOR, params: ConvParam, anno: Anno, __pos: SourceContext): TENSOR = {
    assert(input.et == filter.et && filter.et == doutput.et)
    val res_tt = input.resultType
    (new TENSOR(Adapter.g.reflectRead("tensor_conv_bwd_data", C(res_tt), C(anno),
      input.x, filter.x, doutput.x, C(params))(input.x, filter.x, doutput.x)).withSrcType(__pos, input.et))
  }

  def ConvBackwardFilter(input: TENSOR, filter: TENSOR, doutput: TENSOR, params: ConvParam, anno: Anno, __pos: SourceContext): TENSOR = {
    assert(input.et == filter.et && filter.et == doutput.et)
    val res_tt = filter.resultType
    (new TENSOR(Adapter.g.reflectRead("tensor_conv_bwd_filter", C(res_tt), C(anno),
      input.x, filter.x, doutput.x, C(params))(input.x, filter.x, doutput.x)).withSrcType(__pos, input.et))
  }

  def ConvForwardOutTensorType(input: TENSOR, filter: TENSOR, params: ConvParam): TensorType = {
    val ConvParam(alpha, beta, padding, strides, dilation) = params

    require(input.shapeSize.size == CUDNN_TENSOR_DIM, "input tensor of convolution must be 4D, found: " + input.shapeSize.size)
    require(filter.shapeSize.size == CUDNN_TENSOR_DIM, "input filter of convolution must be 4D, found: " + filter.shapeSize.size)
    require(padding.size == CUDNN_PARAM_DIM, "padding must be sequence of integer of length 2, found: " + padding.size)
    require(strides.size == CUDNN_PARAM_DIM, "strides must be sequence of integer of length 2, found: " + strides.size)
    require(dilation.size == CUDNN_PARAM_DIM, "dilation must be sequence of integer of length 2, found: " + dilation.size)
    require(input.et == filter.et, "input tensor element type must be equal to filter tensor element type")

    val input_shape = input.resultType.shape
    val filter_shape = filter.resultType.shape

    val output_N = input_shape(CUDNN_N).size
    val output_C = filter_shape(CUDNN_C_OUT).size

    def outputDim(inputDim: Int, pad: Int, filterDim: Int, dil: Int, str: Int) =
      1 + (inputDim + 2*pad - (((filterDim-1)*dil)+1)) / str

    val output_H = outputDim(input_shape(CUDNN_H).size, padding(CUDNN_PARAM_H),
      filter_shape(CUDNN_H).size, dilation(CUDNN_PARAM_H), strides(CUDNN_PARAM_H))
    val output_W = outputDim(input_shape(CUDNN_W).size, padding(CUDNN_PARAM_W),
      filter_shape(CUDNN_W).size, dilation(CUDNN_PARAM_W), strides(CUDNN_PARAM_W))

    val output_shape = Seq(
      Size(input.resultType.namedDim(CUDNN_N), output_N),
      Size(filter.resultType.namedDim(CUDNN_C_OUT), output_C),
      Size(dim, output_H),
      Size(dim, output_W))

    TensorType(output_shape, input.et)
  }

  def DropoutForward(input: TENSOR, params: DropoutParam, anno: Anno, __pos: SourceContext): TENSORS = {
    val output_tt = input.resultType
    val dummy_tt = TensorType(input.resultType.shape, manifest[Boolean])  // dummy shape
    val res_tt = List(output_tt, dummy_tt)

    (new TENSORS(Adapter.g.reflectRead("tensors_dropout", C(res_tt), C(anno),
      input.x, C(params))(input.x))).withSrcType(__pos, input.et)
  }

  def DropoutBackward(doutput: TENSOR, reserveSpace: TENSOR, params: DropoutParam, anno: Anno,  __pos: SourceContext): TENSOR = {
    val res_tt = doutput.resultType
    (new TENSOR(Adapter.g.reflectRead("tensor_dropout_bwd", C(res_tt), C(anno),
      doutput.x, reserveSpace.x, C(params))(doutput.x, reserveSpace.x)).withSrcType(__pos, doutput.et))
  }

  // FIXME(feiw): should some mode of Pooling (such as max pooling) have 2 outputs?
  def PoolingForward(input: TENSOR, params: PoolingParam, mode: String, anno: Anno, __pos: SourceContext): TENSOR = {
    val res_tt = PoolingForwardOutTensorType(input, params)
    (new TENSOR(Adapter.g.reflectRead("tensor_pooling", C(res_tt), C(anno),
      input.x, C(params), C(mode))(input.x)).withSrcType(__pos, input.et))
  }

  def PoolingBackward(input: TENSOR, output: TENSOR, doutput: TENSOR, params: PoolingParam, mode: String,  anno: Anno, __pos: SourceContext): TENSOR = {
    val res_tt = input.resultType
    (new TENSOR(Adapter.g.reflectRead("tensor_pooling_bwd", C(res_tt), C(anno),
      input.x, output.x, doutput.x, C(params), C(mode))(input.x, output.x, doutput.x)).withSrcType(__pos, input.et))
  }

  def PoolingForwardOutTensorType(input: TENSOR, params: PoolingParam): TensorType = {
    val PoolingParam(alpha, beta, window, padding, strides) = params

    require(window.size == CUDNN_PARAM_DIM, "window must be sequence of integer of length 2, found: " + window.size)
    require(strides.size == CUDNN_PARAM_DIM, "strides must be sequence of integer of length 2, found: " + strides.size)
    require(padding.size == CUDNN_PARAM_DIM, "padding must be sequence of integer of length 2, found: " + padding.size)

    val input_shape = input.resultType.shape

    val output_N = input_shape(CUDNN_N).size
    val output_C = input_shape(CUDNN_C).size

    def outputDim(inputDim: Int, pad: Int, windowDim: Int, str: Int) =
      1 + (inputDim + 2*pad - windowDim) / str

    val output_H = outputDim(input_shape(CUDNN_H).size, padding(CUDNN_PARAM_H),
      window(CUDNN_PARAM_H), strides(CUDNN_PARAM_H))

    val output_W = outputDim(input_shape(CUDNN_W).size, padding(CUDNN_PARAM_W),
      window(CUDNN_PARAM_W), strides(CUDNN_PARAM_W))

    val output_shape = Seq(
      Size(input.resultType.namedDim(CUDNN_N), output_N),
      Size(input.resultType.namedDim(CUDNN_C), output_C),
      Size(dim, output_H),          // new dim (fresh)
      Size(dim, output_W))          // new dim (fresh)

    TensorType(output_shape, input.et)
  }


  override def mergable_dims(node: Node) = node match {
    // constraints:
    // input.channels = filter.input_channels
    // output.channels = filter.output_channels // not required TODO: remove
    case Node(s, "tensor_conv", tt::Backend.Const(anno:Anno)::(a:Backend.Sym)::(b:Backend.Sym)::Backend.Const(params:ConvParam)::_, _) =>
      val input_type    = (new TENSOR(a, useOldMetadata=true)).resultType
      val filter_type   = (new TENSOR(b, useOldMetadata=true)).resultType
      val output_type   = (new TENSOR(s, useOldMetadata=true)).resultType
      val inputC      = input_type.namedDim(CUDNN_C)
      val outputC     = output_type.namedDim(CUDNN_C)
      val filterCout  = filter_type.namedDim(CUDNN_C_OUT)
      val filterCin   = filter_type.namedDim(CUDNN_C_IN)
      // val res = List((inputC, filterCin), (outputC, filterCout))
      val res = List((inputC, filterCin))
      res

    case Node(s, "tensors_dropout", _, _) => List()
    case Node(s, "tensor_pooling", _, _) => List()

    case _ => super.mergable_dims(node)
  }

  override def aircopCollect(node: Node, forwardNodes: mutable.ArrayBuffer[Node],
    weightNodes: mutable.ArrayBuffer[Node], backwardNodes: mutable.ArrayBuffer[()=>Unit], liftNodes: mutable.Set[Backend.Sym],
    gradMap: GradMapWrapper,
    momentumMap: mutable.HashMap[Backend.Sym, TENSOR],
    transform: Backend.Exp => Backend.Exp) = node match {
      case Node(s, "tensor_conv", tt::Backend.Const(anno:Anno)::(a:Backend.Sym)::(b:Backend.Sym)::Backend.Const(params:ConvParam)::_, _) =>
        implicit val pos = Adapter.oldSourceMap(s)
        // save forward op in forwardNodes
        forwardNodes += node
        liftNodes += a
        liftNodes += b
        // save backward op in backwardNodes
        (() => {
          val x = new TENSOR(transform(a))      // weight
          val y = new TENSOR(transform(b))      // filter
          val a_grad = ConvBackwardData(x, y, gradMap(s), params, anno, pos)
          Accumulate(gradMap(a), a_grad, anno); ()
        }) +=: backwardNodes
        (() => {
          val x = new TENSOR(transform(a))      // weight
          val y = new TENSOR(transform(b))      // filter
          val b_grad = ConvBackwardFilter(x, y, gradMap(s), params, anno, pos)
          Accumulate(gradMap(b), b_grad, anno); ()
        }) +=: backwardNodes

      case Node(s, "tensors_dropout", tt::Backend.Const(anno:Anno)::(a:Backend.Sym)::Backend.Const(params:DropoutParam)::_, _) =>
        implicit val pos = Adapter.oldSourceMap(s)
        // save forward op in forwardNodes
        forwardNodes += node
        liftNodes += s
        // save backward op in backwardNodes
        (() => {
          val x = new TENSORS(transform(s))
          val grads = gradMap.getGradsOfOp(s)
          val g = DropoutBackward(grads(0), TENSORS.getResult(x, 1), params, anno, pos)
          Accumulate(gradMap(a), g, anno); ()
        }) +=: backwardNodes

      case Node(s, "tensor_pooling", tt::Backend.Const(anno:Anno)::(a:Backend.Sym)::Backend.Const(params:PoolingParam)::Backend.Const(mode:String)::_, _) =>
        implicit val pos = Adapter.oldSourceMap(s)
        // save forward op in forwardNodes
        forwardNodes += node
        liftNodes += a
        liftNodes += s
        // save backward op in backwardNodes
        (() => {
            val x = new TENSOR(transform(a))
            val y = new TENSOR(transform(s))
            val grad = PoolingBackward(x, y, gradMap(s), params, mode, anno, pos)
            Accumulate(gradMap(a), grad, anno); ()
        }) +=: backwardNodes

      case _ => super.aircopCollect(node, forwardNodes, weightNodes, backwardNodes, liftNodes, gradMap, momentumMap, transform)
    }

  override def printTensor(node: Node, graph: Graph) = node match {
    case Node(s, "tensor_conv", Backend.Const(tt:TensorType)::Backend.Const(anno:Anno)::(a:Backend.Sym)::(b:Backend.Sym)::_, _) =>
      s"$s = tensor_conv($a, $b) (${symTensorShape(a, graph)}, ${symTensorShape(b, graph)})->${tt.toString}${if (anno != NAnno) s"\nAnno: $anno" else ""}"
    case Node(s, "tensor_conv_bwd_filter", Backend.Const(tt: TensorType)::Backend.Const(anno:Anno)::
      (weight:Backend.Sym)::(filter:Backend.Sym)::(doutput:Backend.Sym)::Backend.Const(params)::_, _) =>
      s"$s = tensor_conv_bwd_filter($weight, $filter, $doutput) (${symTensorShape(weight, graph)}, ${symTensorShape(filter, graph)}, ${symTensorShape(doutput, graph)})->${tt.toString}${if (anno != NAnno) s"\nAnno: $anno" else ""}"
    case Node(s, "tensors_dropout", Backend.Const(List(output_tt:TensorType, dummy_tt:TensorType))::Backend.Const(anno:Anno)::(a:Backend.Sym)::_, _) =>
      s"$s:2 = tensors_dropout($a) (${symTensorShape(a, graph)})->(${output_tt.toString}, ${dummy_tt.toString})${if (anno != NAnno) s"\nAnno: $anno" else ""}"
    case Node(s, "tensor_pooling", Backend.Const(tt:TensorType)::Backend.Const(anno:Anno)::(a:Backend.Sym)::params::Backend.Const(mode:String)::_, _) =>
      s"$s = tensor_pooling($a, mode=$mode) (${symTensorShape(a, graph)})->${tt.toString}${if (anno != NAnno) s"\nAnno: $anno" else ""}"
    case _ => super.printTensor(node, graph)
  }
}

trait FixedSizeDistributedTensorOpsConv extends FixedSizeDistributedTensorOpsBase {
  import FixedSizeDistributedTensorTypeLess._
  import scala.collection.immutable.Seq

  implicit class TensorOpsConv[T:Numeric:Manifest](x: Rep[Tensor[T]]) {
    val self = tensor(x)
    // val conv_params_def = ConvParam(1.0f, 0.0f, Seq(1, 1), Seq(1, 1), Seq(1, 1))  // default convolution parameter settings

    def conv(y: Rep[Tensor[T]], params: ConvParam)(implicit __pos: SourceContext, anno: Anno): Rep[Tensor[T]] = {
      val t = ConvForward(self, tensor(y), params, anno, __pos)
      Wrap[Tensor[T]](t.x)
    }

    def conv(y: Rep[Tensor[T]], params: ConvParam, anno: Anno)(implicit __pos: SourceContext): Rep[Tensor[T]] = {
      val t = ConvForward(self, tensor(y), params, anno, __pos)
      Wrap[Tensor[T]](t.x)
    }

    def dropout(params: DropoutParam)(implicit __pos: SourceContext, anno: Anno): List[Rep[Tensor[T]]] = {
      val op = DropoutForward(self, params, anno, __pos)
      ((0 until 1): Range).toList.map(i => Wrap[Tensor[T]](TENSORS.getResult(op, i).x))
    }

    def dropout(params: DropoutParam, anno: Anno)(implicit __pos: SourceContext): List[Rep[Tensor[T]]] = {
      val op = DropoutForward(self, params, anno, __pos)
      ((0 until 1): Range).toList.map(i => Wrap[Tensor[T]](TENSORS.getResult(op, i).x))
    }

    def maxpool(params: PoolingParam, deterministic: Boolean = false)(implicit __pos: SourceContext, anno: Anno): Rep[Tensor[T]] = {
      val t = PoolingForward(self, params, if (deterministic) "max_dtm" else "max", anno, __pos)
      Wrap[Tensor[T]](t.x)
    }

    def maxpool(params: PoolingParam, deterministic: Boolean, anno: Anno)(implicit __pos: SourceContext): Rep[Tensor[T]] = {
      val t = PoolingForward(self, params, if (deterministic) "max_dtm" else "max", anno, __pos)
      Wrap[Tensor[T]](t.x)
    }

    def avgpool(params: PoolingParam, include_pad: Boolean = true)(implicit __pos: SourceContext, anno: Anno): Rep[Tensor[T]] = {
      val t = PoolingForward(self, params, if (include_pad) "avg_in_pad" else "avg_ex_pad", anno, __pos)
      Wrap[Tensor[T]](t.x)
    }

    def avgpool(params: PoolingParam, include_pad: Boolean, anno: Anno)(implicit __pos: SourceContext): Rep[Tensor[T]] = {
      val t = PoolingForward(self, params, if (include_pad) "avg_in_pad" else "avg_ex_pad", anno, __pos)
      Wrap[Tensor[T]](t.x)
    }
  }
}
