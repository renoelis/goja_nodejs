package buffer

import (
	"bytes"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	stderrors "errors"
	"fmt"
	"math"
	"math/big"
	"reflect"
	"strconv"
	"strings"

	"github.com/dop251/goja"
	"github.com/dop251/goja_nodejs/errors"
	"github.com/dop251/goja_nodejs/goutil"
	"github.com/dop251/goja_nodejs/require"

	"github.com/dop251/base64dec"
	"golang.org/x/text/encoding/unicode"
)

const ModuleName = "buffer"

type Buffer struct {
	r *goja.Runtime

	bufferCtorObj *goja.Object

	uint8ArrayCtorObj *goja.Object
	uint8ArrayCtor    goja.Constructor

	// INSPECT_MAX_BYTES 值（每个 runtime 独立）
	inspectMaxBytesValue float64
}

var (
	symApi = goja.NewSymbol("api")
)

var (
	reflectTypeArrayBuffer = reflect.TypeOf(goja.ArrayBuffer{})
	reflectTypeString      = reflect.TypeOf("")
	reflectTypeInt         = reflect.TypeOf(int64(0))
	reflectTypeFloat       = reflect.TypeOf(0.0)
	reflectTypeBytes       = reflect.TypeOf(([]byte)(nil))
)

func Enable(runtime *goja.Runtime) {
	runtime.Set("Buffer", require.Require(runtime, ModuleName).ToObject(runtime).Get("Buffer"))
}

func Bytes(r *goja.Runtime, v goja.Value) []byte {
	var b []byte
	err := r.ExportTo(v, &b)
	if err != nil {
		return []byte(v.String())
	}
	return b
}

func mod(r *goja.Runtime) *goja.Object {
	res := r.Get("Buffer")
	if res == nil {
		res = require.Require(r, ModuleName).ToObject(r).Get("Buffer")
	}
	m, ok := res.(*goja.Object)
	if !ok {
		panic(r.NewTypeError("Could not extract Buffer"))
	}
	return m
}

func api(mod *goja.Object) *Buffer {
	if s := mod.GetSymbol(symApi); s != nil {
		b, _ := s.Export().(*Buffer)
		return b
	}

	return nil
}

func GetApi(r *goja.Runtime) *Buffer {
	return api(mod(r))
}

// GetInspectMaxBytes 返回当前 runtime 的 INSPECT_MAX_BYTES 值
// 用于 enhance_modules/buffer 的 inspect 方法
func GetInspectMaxBytes(r *goja.Runtime) float64 {
	if bufAPI := GetApi(r); bufAPI != nil {
		return bufAPI.inspectMaxBytesValue
	}
	return 50.0 // 默认值
}

func DecodeBytes(r *goja.Runtime, arg, enc goja.Value) []byte {
	switch arg.ExportType() {
	case reflectTypeArrayBuffer:
		return arg.Export().(goja.ArrayBuffer).Bytes()
	case reflectTypeString:
		var codec StringCodec
		if !goja.IsUndefined(enc) {
			codec = stringCodecs[enc.String()]
		}
		if codec == nil {
			codec = utf8Codec
		}
		return codec.DecodeAppend(arg.String(), nil)
	default:
		if o, ok := arg.(*goja.Object); ok {
			if o.ExportType() == reflectTypeBytes {
				return o.Export().([]byte)
			}
		}
	}
	panic(errors.NewTypeError(r, errors.ErrCodeInvalidArgType, "The \"data\" argument must be of type string or an instance of Buffer, TypedArray, or DataView."))
}

func WrapBytes(r *goja.Runtime, data []byte) *goja.Object {
	m := mod(r)
	if api := api(m); api != nil {
		return api.WrapBytes(data)
	}
	if from, ok := goja.AssertFunction(m.Get("from")); ok {
		ab := r.NewArrayBuffer(data)
		v, err := from(m, r.ToValue(ab))
		if err != nil {
			panic(err)
		}
		return v.ToObject(r)
	}
	panic(r.NewTypeError("Buffer.from is not a function"))
}

// EncodeBytes returns the given byte slice encoded as string with the given encoding. If encoding
// is not specified or not supported, returns a Buffer that wraps the data.
func EncodeBytes(r *goja.Runtime, data []byte, enc goja.Value) goja.Value {
	var codec StringCodec
	if !goja.IsUndefined(enc) {
		codec = StringCodecByName(enc.String())
	}
	if codec != nil {
		return r.ToValue(codec.Encode(data))
	}
	return WrapBytes(r, data)
}

func (b *Buffer) WrapBytes(data []byte) *goja.Object {
	return b.fromBytes(data)
}

func (b *Buffer) ctor(call goja.ConstructorCall) (res *goja.Object) {
	arg := call.Argument(0)
	switch arg.ExportType() {
	case reflectTypeInt, reflectTypeFloat:
		panic(b.r.NewTypeError("Calling the Buffer constructor with numeric argument is not implemented yet"))
		// TODO implement
	}
	return b._from(call.Arguments...)
}

type StringCodec interface {
	DecodeAppend(string, []byte) []byte
	Encode([]byte) string
	Decode(s string) []byte
}

type hexCodec struct{}

func (hexCodec) DecodeAppend(s string, b []byte) []byte {
	l := hex.DecodedLen(len(s))
	dst, res := expandSlice(b, l)
	n, err := hex.Decode(dst, []byte(s))
	if err != nil {
		res = res[:len(b)+n]
	}
	return res
}

func (hexCodec) Decode(s string) []byte {
	n, _ := hex.DecodeString(s)
	return n
}
func (hexCodec) Encode(b []byte) string {
	return hex.EncodeToString(b)
}

type _utf8Codec struct{}

func (c _utf8Codec) DecodeAppend(s string, b []byte) []byte {
	r := c.Decode(s)
	dst, res := expandSlice(b, len(r))
	copy(dst, r)
	return res
}

func (_utf8Codec) Decode(s string) []byte {
	r, _ := unicode.UTF8.NewEncoder().String(s)
	return []byte(r)
}
func (_utf8Codec) Encode(b []byte) string {
	r, _ := unicode.UTF8.NewDecoder().Bytes(b)
	return string(r)
}

type base64Codec struct{}

type base64UrlCodec struct {
	base64Codec
}

func (base64Codec) DecodeAppend(s string, b []byte) []byte {
	res, _ := Base64DecodeAppend(b, s)
	return res
}

func (base64Codec) Decode(s string) []byte {
	res, _ := base64.StdEncoding.DecodeString(s)
	return res
}
func (base64Codec) Encode(b []byte) string {
	return base64.StdEncoding.EncodeToString(b)
}

func (base64UrlCodec) Encode(b []byte) string {
	return base64.RawURLEncoding.EncodeToString(b)
}

var utf8Codec StringCodec = _utf8Codec{}

var stringCodecs = map[string]StringCodec{
	"hex":       hexCodec{},
	"utf8":      utf8Codec,
	"utf-8":     utf8Codec,
	"base64":    base64Codec{},
	"base64Url": base64UrlCodec{},
}

func expandSlice(b []byte, l int) (dst, res []byte) {
	if cap(b)-len(b) < l {
		b1 := make([]byte, len(b)+l)
		copy(b1, b)
		dst = b1[len(b):]
		res = b1
	} else {
		dst = b[len(b) : len(b)+l]
		res = b[:len(b)+l]
	}
	return
}

func Base64DecodeAppend(dst []byte, src string) ([]byte, error) {
	l := base64.RawStdEncoding.DecodedLen(len(src))
	d, res := expandSlice(dst, l)
	n, err := base64dec.DecodeBase64(d, src)

	res = res[:len(dst)+n]
	return res, err
}

func (b *Buffer) fromString(str, enc string) *goja.Object {
	codec := stringCodecs[enc]
	if codec == nil {
		codec = utf8Codec
	}
	return b.fromBytes(codec.DecodeAppend(str, nil))
}

func (b *Buffer) fromBytes(data []byte) *goja.Object {
	o, err := b.uint8ArrayCtor(b.bufferCtorObj, b.r.ToValue(b.r.NewArrayBuffer(data)))
	if err != nil {
		panic(err)
	}
	return o
}

func (b *Buffer) _from(args ...goja.Value) *goja.Object {
	if len(args) == 0 {
		panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType, "The first argument must be of type string or an instance of Buffer, ArrayBuffer, or Array or an Array-like Object. Received undefined"))
	}
	arg := args[0]

	switch arg.ExportType() {
	case reflectTypeArrayBuffer:
		// 尝试导出为 ArrayBuffer
		ab := arg.Export().(goja.ArrayBuffer)
		abLen := int64(len(ab.Bytes()))

		// 验证 offset 和 length 参数
		// 检查 offset 参数
		if len(args) > 1 && !goja.IsUndefined(args[1]) {
			offset := args[1].ToInteger()
			if offset < 0 {
				panic(errors.NewRangeError(b.r, errors.ErrCodeOutOfRange, "The value of \"offset\" is out of range. It must be >= 0. Received %d", offset))
			}
			if offset > abLen {
				panic(errors.NewRangeError(b.r, errors.ErrCodeOutOfRange, "The value of \"offset\" is out of range. It must be <= %d. Received %d", abLen, offset))
			}

			// 检查 length 参数
			if len(args) > 2 && !goja.IsUndefined(args[2]) {
				length := args[2].ToInteger()
				// 🔥 修复：Node.js v25.0.0 行为 - 负数 length 创建空 Buffer (length=0)
				// goja 的 Uint8Array 构造函数会对负数 length 抛出错误，需要先处理
				if length < 0 {
					// 负数 length：修改 args[2] 为 0，创建空 Buffer
					args[2] = b.r.ToValue(0)
				} else if offset+length > abLen {
					// 正数 length：检查是否超出 ArrayBuffer 范围
					panic(errors.NewRangeError(b.r, errors.ErrCodeOutOfRange, "The value of \"length\" is out of range. It must be <= %d. Received %d", abLen-offset, length))
				}
			}
		}

		v, err := b.uint8ArrayCtor(b.bufferCtorObj, args...)
		if err != nil {
			panic(err)
		}
		return v
	case reflectTypeString:
		var enc string
		if len(args) > 1 {
			enc = args[1].String()
		}
		return b.fromString(arg.String(), enc)
	default:
		if o, ok := arg.(*goja.Object); ok {
			// 在处理之前，先检查是否是 Symbol 或函数类型

			// 检查是否是函数 - 必须在其他检查之前
			if _, isFunc := goja.AssertFunction(arg); isFunc {
				panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType, "The first argument must be of type string or an instance of Buffer, ArrayBuffer, or Array or an Array-like Object. Received function"))
			}

			// 检查是否是 Symbol - Symbol 对象有特殊的 description 属性
			// 并且不应该有 byteLength 属性（排除真正的 ArrayBuffer）
			desc := o.Get("description")
			byteLength := o.Get("byteLength")
			if desc != nil && !goja.IsUndefined(desc) && (byteLength == nil || goja.IsUndefined(byteLength)) {
				// 可能是 Symbol，进一步检查
				// Symbol 不能被当作字符串或其他类型处理
				// 尝试调用 Symbol.prototype.toString，如果成功且返回 "Symbol(...)"，则确认是 Symbol
				toStr := o.Get("toString")
				if f, ok := goja.AssertFunction(toStr); ok {
					result, err := f(o)
					if err == nil && result != nil {
						strResult := result.String()
						if len(strResult) >= 7 && strResult[:7] == "Symbol(" {
							panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType, "The first argument must be of type string or an instance of Buffer, ArrayBuffer, or Array or an Array-like Object. Received symbol"))
						}
					}
				}
			}

			if o.ExportType() == reflectTypeBytes {
				bb, _ := o.Export().([]byte)
				a := make([]byte, len(bb))
				copy(a, bb)
				return b.fromBytes(a)
			} else {
				if f, ok := goja.AssertFunction(o.Get("valueOf")); ok {
					valueOf, err := f(o)
					if err != nil {
						panic(err)
					}
					if valueOf != o {
						args[0] = valueOf
						return b._from(args...)
					}
				}

				if s := o.GetSymbol(goja.SymToPrimitive); s != nil {
					if f, ok := goja.AssertFunction(s); ok {
						str, err := f(o, b.r.ToValue("string"))
						if err != nil {
							panic(err)
						}
						args[0] = str
						return b._from(args...)
					}
				}
			}
			// array-like
			if v := o.Get("length"); v != nil {
				length := int(v.ToInteger())
				a := make([]byte, length)
				for i := 0; i < length; i++ {
					item := o.Get(strconv.Itoa(i))
					if item != nil {
						a[i] = byte(item.ToInteger())
					}
				}
				return b.fromBytes(a)
			}
		}
	}
	panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType, "The first argument must be of type string or an instance of Buffer, ArrayBuffer, or Array or an Array-like Object. Received %s", arg))
}

func (b *Buffer) from(call goja.FunctionCall) goja.Value {
	return b._from(call.Arguments...)
}

func StringCodecByName(name string) StringCodec {
	return stringCodecs[name]
}

func (b *Buffer) getStringCodec(enc goja.Value) (codec StringCodec) {
	if !goja.IsUndefined(enc) {
		codec = stringCodecs[enc.String()]
		if codec == nil {
			panic(errors.NewTypeError(b.r, "ERR_UNKNOWN_ENCODING", "Unknown encoding: %s", enc))
		}
	} else {
		codec = utf8Codec
	}
	return
}

func (b *Buffer) fill(buf []byte, fill string, enc goja.Value) []byte {
	codec := b.getStringCodec(enc)
	b1 := codec.DecodeAppend(fill, buf[:0])
	if len(b1) > len(buf) {
		return b1[:len(buf)]
	}
	for i := len(b1); i < len(buf); {
		i += copy(buf[i:], buf[:i])
	}
	return buf
}

func (b *Buffer) alloc(call goja.FunctionCall) goja.Value {
	arg0 := call.Argument(0)
	size := -1
	if goja.IsNumber(arg0) {
		size = int(arg0.ToInteger())
	}
	if size < 0 {
		panic(errors.NewArgumentNotNumberTypeError(b.r, "size"))
	}
	fill := call.Argument(1)
	buf := make([]byte, size)
	if !goja.IsUndefined(fill) {
		if goja.IsString(fill) {
			var enc goja.Value
			if a := call.Argument(2); goja.IsString(a) {
				enc = a
			} else {
				enc = goja.Undefined()
			}
			buf = b.fill(buf, fill.String(), enc)
		} else {
			fill = fill.ToNumber()
			if !goja.IsNaN(fill) && !goja.IsInfinity(fill) {
				fillByte := byte(fill.ToInteger())
				if fillByte != 0 {
					for i := range buf {
						buf[i] = fillByte
					}
				}
			}
		}
	}
	return b.fromBytes(buf)
}

func (b *Buffer) proto_toString(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	codec := b.getStringCodec(call.Argument(0))
	start := goutil.CoercedIntegerArgument(call, 1, 0, 0)

	// Node's Buffer class makes this zero if it is negative
	if start < 0 {
		start = 0
	} else if start >= int64(len(bb)) {
		// returns an empty string if start is beyond the length of the buffer
		return b.r.ToValue("")
	}

	// NOTE that Node will default to the length of the buffer, but uses 0 for type mismatch defaults
	end := goutil.CoercedIntegerArgument(call, 2, int64(len(bb)), 0)
	if end < 0 || start >= end {
		// returns an empty string if end < 0 or start >= end
		return b.r.ToValue("")
	} else if end > int64(len(bb)) {
		// and Node ensures you don't go past the Buffer
		end = int64(len(bb))
	}

	return b.r.ToValue(codec.Encode(bb[start:end]))
}

func (b *Buffer) proto_equals(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	other := call.Argument(0)
	if b.r.InstanceOf(other, b.uint8ArrayCtorObj) {
		otherBytes := Bytes(b.r, other)
		return b.r.ToValue(bytes.Equal(bb, otherBytes))
	}
	panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType, "The \"otherBuffer\" argument must be an instance of Buffer or Uint8Array."))
}

// proto_inspect 实现 Buffer.prototype.inspect() 方法
// 根据 INSPECT_MAX_BYTES 的值截断显示
// 注意：此方法可能会被 enhance_modules/buffer/write_methods.go 覆盖
func (b *Buffer) proto_inspect(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	maxBytes := b.inspectMaxBytesValue
	return b.formatInspect(bb, maxBytes)
}

// formatInspect 格式化 Buffer 的 inspect 输出
func (b *Buffer) formatInspect(bb []byte, maxBytes float64) goja.Value {
	var result strings.Builder
	result.WriteString("<Buffer ")

	// 🔥 修复：处理 Number.MAX_VALUE 等极大值的溢出
	// 将浮点数 maxBytes 转换为实际显示的字节数（向下取整用于索引）
	totalBytes := len(bb)
	var displayBytes int

	// 检查是否超出 int 最大值（避免溢出）
	// math.MaxInt = 9223372036854775807 (int64 on 64-bit systems)
	if maxBytes > float64(math.MaxInt) || math.IsInf(maxBytes, 1) {
		// 极大值或 +Infinity：显示全部字节
		displayBytes = totalBytes
	} else {
		displayBytes = int(math.Floor(maxBytes))
		if displayBytes > totalBytes {
			displayBytes = totalBytes
		}
	}

	truncated := displayBytes < totalBytes

	// 显示字节（十六进制格式）
	for i := 0; i < displayBytes; i++ {
		if i > 0 {
			result.WriteString(" ")
		}
		result.WriteString(fmt.Sprintf("%02x", bb[i]))
	}

	// 如果被截断，显示剩余字节数（保留浮点数）
	if truncated {
		remaining := float64(totalBytes) - maxBytes
		// 格式化：如果是整数显示为整数，否则显示为浮点数
		if remaining == math.Floor(remaining) {
			result.WriteString(fmt.Sprintf(" ... %d more bytes", int(remaining)))
		} else {
			result.WriteString(fmt.Sprintf(" ... %g more bytes", remaining))
		}
	}

	result.WriteString(">")
	return b.r.ToValue(result.String())
}

// readBigInt64BE reads a big-endian 64-bit signed integer from the buffer
func (b *Buffer) readBigInt64BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := int64(binary.BigEndian.Uint64(bb[offset : offset+8]))

	return b.r.ToValue(big.NewInt(value))
}

// readBigInt64LE reads a little-endian 64-bit signed integer from the buffer
func (b *Buffer) readBigInt64LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := int64(binary.LittleEndian.Uint64(bb[offset : offset+8]))

	return b.r.ToValue(big.NewInt(value))
}

// readBigUInt64BE reads a big-endian 64-bit unsigned integer from the buffer
func (b *Buffer) readBigUInt64BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := binary.BigEndian.Uint64(bb[offset : offset+8])

	return b.r.ToValue(new(big.Int).SetUint64(value))
}

// readBigUInt64LE reads a little-endian 64-bit unsigned integer from the buffer
func (b *Buffer) readBigUInt64LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := binary.LittleEndian.Uint64(bb[offset : offset+8])

	return b.r.ToValue(new(big.Int).SetUint64(value))
}

// readDoubleBE reads a big-endian 64-bit floating-point number from the buffer
func (b *Buffer) readDoubleBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := binary.BigEndian.Uint64(bb[offset : offset+8])

	return b.r.ToValue(math.Float64frombits(value))
}

// readDoubleLE reads a little-endian 64-bit floating-point number from the buffer
func (b *Buffer) readDoubleLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 8)
	value := binary.LittleEndian.Uint64(bb[offset : offset+8])

	return b.r.ToValue(math.Float64frombits(value))
}

// readFloatBE reads a big-endian 32-bit floating-point number from the buffer
func (b *Buffer) readFloatBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := binary.BigEndian.Uint32(bb[offset : offset+4])

	return b.r.ToValue(math.Float32frombits(value))
}

// readFloatLE reads a little-endian 32-bit floating-point number from the buffer
func (b *Buffer) readFloatLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := binary.LittleEndian.Uint32(bb[offset : offset+4])

	return b.r.ToValue(math.Float32frombits(value))
}

// readInt8 reads an 8-bit signed integer from the buffer
func (b *Buffer) readInt8(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 1)
	value := int8(bb[offset])

	return b.r.ToValue(value)
}

// readInt16BE reads a big-endian 16-bit signed integer from the buffer
func (b *Buffer) readInt16BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 2)
	value := int16(binary.BigEndian.Uint16(bb[offset : offset+2]))

	return b.r.ToValue(value)
}

// readInt16LE reads a little-endian 16-bit signed integer from the buffer
func (b *Buffer) readInt16LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 2)
	value := int16(binary.LittleEndian.Uint16(bb[offset : offset+2]))

	return b.r.ToValue(value)
}

// readInt32BE reads a big-endian 32-bit signed integer from the buffer
func (b *Buffer) readInt32BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := int32(binary.BigEndian.Uint32(bb[offset : offset+4]))

	return b.r.ToValue(value)
}

// readInt32LE reads a little-endian 32-bit signed integer from the buffer
func (b *Buffer) readInt32LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := int32(binary.LittleEndian.Uint32(bb[offset : offset+4]))

	return b.r.ToValue(value)
}

// readIntBE reads a big-endian signed integer of variable byte length
func (b *Buffer) readIntBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset, byteLength := b.getVariableLengthReadArguments(call, bb)

	var value int64
	for i := int64(0); i < byteLength; i++ {
		value = (value << 8) | int64(bb[offset+i])
	}

	value = signExtend(value, byteLength)

	return b.r.ToValue(value)
}

// readIntLE reads a little-endian signed integer of variable byte length
func (b *Buffer) readIntLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset, byteLength := b.getVariableLengthReadArguments(call, bb)

	var value int64
	for i := byteLength - 1; i >= 0; i-- {
		value = (value << 8) | int64(bb[offset+i])
	}

	value = signExtend(value, byteLength)

	return b.r.ToValue(value)
}

// readUInt8 reads an 8-bit unsigned integer from the buffer
func (b *Buffer) readUInt8(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 1)
	value := bb[offset]

	return b.r.ToValue(value)
}

// readUInt16BE reads a big-endian 16-bit unsigned integer from the buffer
func (b *Buffer) readUInt16BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 2)
	value := binary.BigEndian.Uint16(bb[offset : offset+2])

	return b.r.ToValue(value)
}

// readUInt16LE reads a little-endian 16-bit unsigned integer from the buffer
func (b *Buffer) readUInt16LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 2)
	value := binary.LittleEndian.Uint16(bb[offset : offset+2])

	return b.r.ToValue(value)
}

// readUInt32BE reads a big-endian 32-bit unsigned integer from the buffer
func (b *Buffer) readUInt32BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := binary.BigEndian.Uint32(bb[offset : offset+4])

	return b.r.ToValue(value)
}

// readUInt32LE reads a little-endian 32-bit unsigned integer from the buffer
func (b *Buffer) readUInt32LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset := b.getOffsetArgument(call, 0, bb, 4)
	value := binary.LittleEndian.Uint32(bb[offset : offset+4])

	return b.r.ToValue(value)
}

// readUIntBE reads a big-endian unsigned integer of variable byte length
func (b *Buffer) readUIntBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset, byteLength := b.getVariableLengthReadArguments(call, bb)

	var value uint64
	for i := int64(0); i < byteLength; i++ {
		value = (value << 8) | uint64(bb[offset+i])
	}

	return b.r.ToValue(value)
}

// readUIntLE reads a little-endian unsigned integer of variable byte length
func (b *Buffer) readUIntLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	offset, byteLength := b.getVariableLengthReadArguments(call, bb)

	var value uint64
	for i := byteLength - 1; i >= 0; i-- {
		value = (value << 8) | uint64(bb[offset+i])
	}

	return b.r.ToValue(value)
}

// write will write a string to the Buffer at offset according to the character encoding. The length parameter is
// the number of bytes to write. If buffer did not contain enough space to fit the entire string, only part of string
// will be written.
func (b *Buffer) write(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	str := goutil.RequiredStringArgument(b.r, call, "string", 0)
	// note that we are passing in zero for numBytes, since the length parameter, which depends on offset,
	// will dictate the number of bytes
	offset := b.getOffsetArgument(call, 1, bb, 0)
	// the length defaults to the size of the buffer - offset
	maxLength := int64(len(bb)) - offset
	length := goutil.OptionalIntegerArgument(b.r, call, "length", 2, maxLength)
	codec := b.getStringCodec(call.Argument(3))

	raw := codec.Decode(str)
	if int64(len(raw)) < length {
		// make sure we only write up to raw bytes
		length = int64(len(raw))
	}
	n := copy(bb[offset:], raw[:length])
	return b.r.ToValue(n)
}

// writeBigInt64BE writes a big-endian 64-bit signed integer to the buffer
func (b *Buffer) writeBigInt64BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredBigIntArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	intValue := value.Int64()
	binary.BigEndian.PutUint64(bb[offset:offset+8], uint64(intValue))

	return b.r.ToValue(offset + 8)
}

// writeBigInt64LE writes a little-endian 64-bit signed integer to the buffer
func (b *Buffer) writeBigInt64LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredBigIntArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	intValue := value.Int64()
	binary.LittleEndian.PutUint64(bb[offset:offset+8], uint64(intValue))

	return b.r.ToValue(offset + 8)
}

// writeBigUInt64BE writes a big-endian 64-bit unsigned integer to the buffer
func (b *Buffer) writeBigUInt64BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredBigIntArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	uintValue := value.Uint64()
	binary.BigEndian.PutUint64(bb[offset:offset+8], uintValue)

	return b.r.ToValue(offset + 8)
}

// writeBigUInt64LE writes a little-endian 64-bit unsigned integer to the buffer
func (b *Buffer) writeBigUInt64LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredBigIntArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	uintValue := value.Uint64()
	binary.LittleEndian.PutUint64(bb[offset:offset+8], uintValue)

	return b.r.ToValue(offset + 8)
}

// writeDoubleBE writes a big-endian 64-bit double to the buffer
func (b *Buffer) writeDoubleBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredFloatArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	bits := math.Float64bits(value)
	binary.BigEndian.PutUint64(bb[offset:offset+8], bits)

	return b.r.ToValue(offset + 8)
}

// writeDoubleLE writes a little-endian 64-bit double to the buffer
func (b *Buffer) writeDoubleLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredFloatArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 8)

	bits := math.Float64bits(value)
	binary.LittleEndian.PutUint64(bb[offset:offset+8], bits)

	return b.r.ToValue(offset + 8)
}

// writeFloatBE writes a big-endian 32-bit float to the buffer
func (b *Buffer) writeFloatBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredFloatArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinFloat32Range(value)

	bits := math.Float32bits(float32(value))
	binary.BigEndian.PutUint32(bb[offset:offset+4], bits)

	return b.r.ToValue(offset + 4)
}

// writeFloatLE writes a little-endian 32-bit floating-point number to the buffer
func (b *Buffer) writeFloatLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredFloatArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinFloat32Range(value)

	bits := math.Float32bits(float32(value))
	binary.LittleEndian.PutUint32(bb[offset:offset+4], bits)

	return b.r.ToValue(offset + 4)
}

// writeInt8 writes an 8-bit signed integer to the buffer
func (b *Buffer) writeInt8(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 1)

	if value < math.MinInt8 || value > math.MaxInt8 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}

	bb[offset] = byte(int8(value))

	return b.r.ToValue(offset + 1)
}

// writeInt16BE writes a big-endian 16-bit signed integer to the buffer
func (b *Buffer) writeInt16BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 2)

	b.ensureWithinInt16Range(value)

	binary.BigEndian.PutUint16(bb[offset:offset+2], uint16(value))

	return b.r.ToValue(offset + 2)
}

// writeInt16LE writes a little-endian 16-bit signed integer to the buffer
func (b *Buffer) writeInt16LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 2)

	b.ensureWithinInt16Range(value)

	binary.LittleEndian.PutUint16(bb[offset:offset+2], uint16(value))

	return b.r.ToValue(offset + 2)
}

// writeInt32BE writes a big-endian 32-bit signed integer to the buffer
func (b *Buffer) writeInt32BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinInt32Range(value)

	binary.BigEndian.PutUint32(bb[offset:offset+4], uint32(value))

	return b.r.ToValue(offset + 4)
}

// writeInt32LE writes a little-endian 32-bit signed integer to the buffer
func (b *Buffer) writeInt32LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinInt32Range(value)

	binary.LittleEndian.PutUint32(bb[offset:offset+4], uint32(value))

	return b.r.ToValue(offset + 4)
}

// writeIntBE writes a big-endian signed integer of variable byte length
func (b *Buffer) writeIntBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset, byteLength := b.getVariableLengthWriteArguments(call, bb)

	b.ensureWithinIntRange(byteLength, value)

	// Write bytes in big-endian order (most significant byte first)
	for i := int64(0); i < byteLength; i++ {
		shift := uint(8 * (byteLength - 1 - i))
		bb[offset+i] = byte(value >> shift)
	}

	return b.r.ToValue(offset + byteLength)
}

// writeIntLE writes a little-endian signed integer of variable byte length
func (b *Buffer) writeIntLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset, byteLength := b.getVariableLengthWriteArguments(call, bb)

	b.ensureWithinIntRange(byteLength, value)

	// Write bytes in little-endian order
	for i := int64(0); i < byteLength; i++ {
		shift := uint(8 * i)
		bb[offset+i] = byte(value >> shift)
	}

	return b.r.ToValue(offset + byteLength)
}

// writeUInt8 writes an 8-bit unsigned integer to the buffer
func (b *Buffer) writeUInt8(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 1)

	if value < 0 || value > 255 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}

	bb[offset] = uint8(value)

	return b.r.ToValue(offset + 1)
}

// writeUInt16BE writes a big-endian 16-bit unsigned integer to the buffer
func (b *Buffer) writeUInt16BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 2)

	b.ensureWithinUInt16Range(value)

	binary.BigEndian.PutUint16(bb[offset:offset+2], uint16(value))

	return b.r.ToValue(offset + 2)
}

// writeUInt16LE writes a little-endian 16-bit unsigned integer to the buffer
func (b *Buffer) writeUInt16LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 2)

	b.ensureWithinUInt16Range(value)

	binary.LittleEndian.PutUint16(bb[offset:offset+2], uint16(value))

	return b.r.ToValue(offset + 2)
}

// writeUInt32BE writes a big-endian 32-bit unsigned integer to the buffer
func (b *Buffer) writeUInt32BE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinUInt32Range(value)

	binary.BigEndian.PutUint32(bb[offset:offset+4], uint32(value))

	return b.r.ToValue(offset + 4)
}

// writeUInt32LE writes a little-endian 32-bit unsigned integer to the buffer
func (b *Buffer) writeUInt32LE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset := b.getOffsetArgument(call, 1, bb, 4)

	b.ensureWithinUInt32Range(value)

	binary.LittleEndian.PutUint32(bb[offset:offset+4], uint32(value))

	return b.r.ToValue(offset + 4)
}

// writeUIntBE writes a big-endian unsigned integer of variable byte length
func (b *Buffer) writeUIntBE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset, byteLength := b.getVariableLengthWriteArguments(call, bb)

	b.ensureWithinUIntRange(byteLength, value)

	// Write the bytes in big-endian order (most significant byte first)
	for i := int64(0); i < byteLength; i++ {
		shift := (byteLength - 1 - i) * 8
		bb[offset+i] = byte(value >> shift)
	}

	return b.r.ToValue(offset + byteLength)
}

// writeUIntLE writes a little-endian unsigned integer of variable byte length
func (b *Buffer) writeUIntLE(call goja.FunctionCall) goja.Value {
	bb := Bytes(b.r, call.This)
	value := goutil.RequiredIntegerArgument(b.r, call, "value", 0)
	offset, byteLength := b.getVariableLengthWriteArguments(call, bb)

	b.ensureWithinUIntRange(byteLength, value)

	// Write the bytes in little-endian order
	for i := int64(0); i < byteLength; i++ {
		shift := uint(8 * i)
		bb[offset+i] = byte(value >> shift)
	}

	return b.r.ToValue(offset + byteLength)
}

func (b *Buffer) getOffsetArgument(call goja.FunctionCall, argIndex int, bb []byte, numBytes int64) int64 {
	offset := goutil.OptionalIntegerArgument(b.r, call, "offset", argIndex, 0)

	if offset < 0 || offset+numBytes > int64(len(bb)) {
		panic(errors.NewArgumentOutOfRangeError(b.r, "offset", offset))
	}

	return offset
}

func (b *Buffer) getVariableLengthReadArguments(call goja.FunctionCall, bb []byte) (int64, int64) {
	return b.getVariableLengthArguments(call, bb, 0, 1)
}

func (b *Buffer) getVariableLengthWriteArguments(call goja.FunctionCall, bb []byte) (int64, int64) {
	return b.getVariableLengthArguments(call, bb, 1, 2)
}

func (b *Buffer) getVariableLengthArguments(call goja.FunctionCall, bb []byte, offsetArgIndex, byteLengthArgIndex int) (int64, int64) {
	offset := goutil.RequiredIntegerArgument(b.r, call, "offset", offsetArgIndex)
	byteLength := goutil.RequiredIntegerArgument(b.r, call, "byteLength", byteLengthArgIndex)

	if byteLength < 1 || byteLength > 6 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "byteLength", byteLength))
	}
	if offset < 0 || offset+byteLength > int64(len(bb)) {
		panic(errors.NewArgumentOutOfRangeError(b.r, "offset", offset))
	}

	return offset, byteLength
}

func (b *Buffer) ensureWithinFloat32Range(value float64) {
	if value < -math.MaxFloat32 || value > math.MaxFloat32 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

func (b *Buffer) ensureWithinInt16Range(value int64) {
	if value < math.MinInt16 || value > math.MaxInt16 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

func (b *Buffer) ensureWithinInt32Range(value int64) {
	if value < math.MinInt32 || value > math.MaxInt32 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

// ensureWithinIntRange checks to make sure that value is within the integer range
// defined by the byteLength. Note that byteLength can be at most 6 bytes, so a
// 48 bit integer is the largest possible value.
func (b *Buffer) ensureWithinIntRange(byteLength, value int64) {
	// Calculate the valid range for the given byte length
	bits := byteLength * 8
	minValue := -(int64(1) << (bits - 1))
	maxValue := (int64(1) << (bits - 1)) - 1

	if value < minValue || value > maxValue {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

func (b *Buffer) ensureWithinUInt16Range(value int64) {
	if value < 0 || value > math.MaxUint16 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

func (b *Buffer) ensureWithinUInt32Range(value int64) {
	if value < 0 || value > math.MaxUint32 {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

// ensureWithinUIntRange checks to make sure that value is within the unsigned integer
// range defined by the byteLength. Note that byteLength can be at most 6 bytes, so a
// 48 bit unsigned integer is the largest possible value.
func (b *Buffer) ensureWithinUIntRange(byteLength, value int64) {
	// Validate that the value is within the valid range for the given byteLength
	maxValue := (int64(1) << (8 * byteLength)) - 1
	if value < 0 || value > maxValue {
		panic(errors.NewArgumentOutOfRangeError(b.r, "value", value))
	}
}

func signExtend(value int64, numBytes int64) int64 {
	// we don't have to turn this to a uint64 first because numBytes < 8 so
	// the sign bit will never pushed out of the int64 range
	return (value << (64 - 8*numBytes)) >> (64 - 8*numBytes)
}

func Require(runtime *goja.Runtime, module *goja.Object) {
	b := &Buffer{
		r:                    runtime,
		inspectMaxBytesValue: 50, // 默认值
	}
	uint8Array := runtime.Get("Uint8Array")
	if c, ok := goja.AssertConstructor(uint8Array); ok {
		b.uint8ArrayCtor = c
	} else {
		panic(runtime.NewTypeError("Uint8Array is not a constructor"))
	}
	uint8ArrayObj := uint8Array.ToObject(runtime)

	ctor := runtime.ToValue(b.ctor).ToObject(runtime)
	ctor.SetPrototype(uint8ArrayObj)
	ctor.DefineDataPropertySymbol(symApi, runtime.ToValue(b), goja.FLAG_FALSE, goja.FLAG_FALSE, goja.FLAG_FALSE)
	b.bufferCtorObj = ctor
	b.uint8ArrayCtorObj = uint8ArrayObj

	proto := runtime.NewObject()
	proto.SetPrototype(uint8ArrayObj.Get("prototype").ToObject(runtime))
	proto.DefineDataProperty("constructor", ctor, goja.FLAG_TRUE, goja.FLAG_TRUE, goja.FLAG_FALSE)
	proto.Set("equals", b.proto_equals)
	proto.Set("toString", b.proto_toString)
	proto.Set("inspect", b.proto_inspect)
	proto.Set("readBigInt64BE", b.readBigInt64BE)
	proto.Set("readBigInt64LE", b.readBigInt64LE)
	proto.Set("readBigUInt64BE", b.readBigUInt64BE)
	// aliases for readBigUInt64BE
	proto.Set("readBigUint64BE", b.readBigUInt64BE)

	proto.Set("readBigUInt64LE", b.readBigUInt64LE)
	// aliases for readBigUInt64LE
	proto.Set("readBigUint64LE", b.readBigUInt64LE)

	proto.Set("readDoubleBE", b.readDoubleBE)
	proto.Set("readDoubleLE", b.readDoubleLE)
	proto.Set("readFloatBE", b.readFloatBE)
	proto.Set("readFloatLE", b.readFloatLE)
	proto.Set("readInt8", b.readInt8)
	proto.Set("readInt16BE", b.readInt16BE)
	proto.Set("readInt16LE", b.readInt16LE)
	proto.Set("readInt32BE", b.readInt32BE)
	proto.Set("readInt32LE", b.readInt32LE)
	proto.Set("readIntBE", b.readIntBE)
	proto.Set("readIntLE", b.readIntLE)
	proto.Set("readUInt8", b.readUInt8)
	// aliases for readUInt8
	proto.Set("readUint8", b.readUInt8)

	proto.Set("readUInt16BE", b.readUInt16BE)
	// aliases for readUInt16BE
	proto.Set("readUint16BE", b.readUInt16BE)

	proto.Set("readUInt16LE", b.readUInt16LE)
	// aliases for readUInt16LE
	proto.Set("readUint16LE", b.readUInt16LE)

	proto.Set("readUInt32BE", b.readUInt32BE)
	// aliases for readUInt32BE
	proto.Set("readUint32BE", b.readUInt32BE)

	proto.Set("readUInt32LE", b.readUInt32LE)
	// aliases for readUInt32LE
	proto.Set("readUint32LE", b.readUInt32LE)

	proto.Set("readUIntBE", b.readUIntBE)
	// aliases for readUIntBE
	proto.Set("readUintBE", b.readUIntBE)

	proto.Set("readUIntLE", b.readUIntLE)
	// aliases for readUIntLE
	proto.Set("readUintLE", b.readUIntLE)
	proto.Set("write", b.write)
	proto.Set("writeBigInt64BE", b.writeBigInt64BE)
	proto.Set("writeBigInt64LE", b.writeBigInt64LE)
	proto.Set("writeBigUInt64BE", b.writeBigUInt64BE)
	// aliases for writeBigUInt64BE
	proto.Set("writeBigUint64BE", b.writeBigUInt64BE)

	proto.Set("writeBigUInt64LE", b.writeBigUInt64LE)
	// aliases for writeBigUInt64LE
	proto.Set("writeBigUint64LE", b.writeBigUInt64LE)

	proto.Set("writeDoubleBE", b.writeDoubleBE)
	proto.Set("writeDoubleLE", b.writeDoubleLE)
	proto.Set("writeFloatBE", b.writeFloatBE)
	proto.Set("writeFloatLE", b.writeFloatLE)
	proto.Set("writeInt8", b.writeInt8)
	proto.Set("writeInt16BE", b.writeInt16BE)
	proto.Set("writeInt16LE", b.writeInt16LE)
	proto.Set("writeInt32BE", b.writeInt32BE)
	proto.Set("writeInt32LE", b.writeInt32LE)
	proto.Set("writeIntBE", b.writeIntBE)
	proto.Set("writeIntLE", b.writeIntLE)
	proto.Set("writeUInt8", b.writeUInt8)
	// aliases for writeUInt8
	proto.Set("writeUint8", b.writeUInt8)

	proto.Set("writeUInt16BE", b.writeUInt16BE)
	// aliases for writeUInt16BE
	proto.Set("writeUint16BE", b.writeUInt16BE)

	proto.Set("writeUInt16LE", b.writeUInt16LE)
	// aliases for writeUInt16LE
	proto.Set("writeUint16LE", b.writeUInt16LE)

	proto.Set("writeUInt32BE", b.writeUInt32BE)
	// aliases for writeUInt32BE
	proto.Set("writeUint32BE", b.writeUInt32BE)

	proto.Set("writeUInt32LE", b.writeUInt32LE)
	// aliases for writeUInt32LE
	proto.Set("writeUint32LE", b.writeUInt32LE)

	proto.Set("writeUIntBE", b.writeUIntBE)
	// aliases for writeUIntBE
	proto.Set("writeUintBE", b.writeUIntBE)

	proto.Set("writeUIntLE", b.writeUIntLE)
	// aliases for writeUIntLE
	proto.Set("writeUintLE", b.writeUIntLE)

	ctor.Set("prototype", proto)
	ctor.Set("poolSize", 8192)
	ctor.Set("from", b.from)
	ctor.Set("alloc", b.alloc)

	exports := module.Get("exports").(*goja.Object)
	exports.Set("Buffer", ctor)

	// 导出 constants 对象（Node.js 兼容）
	// 参考：https://nodejs.org/api/buffer.html#bufferconstants
	constantsObj := b.r.NewObject()
	constantsObj.DefineDataProperty(
		"MAX_LENGTH",
		b.r.ToValue(9007199254740991), // Number.MAX_SAFE_INTEGER
		goja.FLAG_FALSE,               // writable
		goja.FLAG_FALSE,               // configurable
		goja.FLAG_TRUE,                // enumerable
	)
	constantsObj.DefineDataProperty(
		"MAX_STRING_LENGTH",
		b.r.ToValue(536870888), // Node.js v25 的值
		goja.FLAG_FALSE,        // writable
		goja.FLAG_FALSE,        // configurable
		goja.FLAG_TRUE,         // enumerable
	)
	exports.Set("constants", constantsObj)

	// 导出常量别名（Node.js v25 兼容）
	// kMaxLength: buffer 模块的 MAX_LENGTH 别名
	kMaxLength := int64(9007199254740991) // Number.MAX_SAFE_INTEGER
	exports.DefineDataProperty(
		"kMaxLength",
		b.r.ToValue(kMaxLength),
		goja.FLAG_FALSE, // writable
		goja.FLAG_FALSE, // configurable
		goja.FLAG_TRUE,  // enumerable
	)

	// kStringMaxLength: buffer 模块的 MAX_STRING_LENGTH 别名
	kStringMaxLength := int64(536870888) // 2^29 - 24
	exports.DefineDataProperty(
		"kStringMaxLength",
		b.r.ToValue(kStringMaxLength),
		goja.FLAG_FALSE, // writable
		goja.FLAG_FALSE, // configurable
		goja.FLAG_TRUE,  // enumerable
	)

	// INSPECT_MAX_BYTES: util.inspect 使用的最大字节数
	// 需要使用 accessor property 来验证输入（与 Node.js v25.0.0 对齐）
	inspectMaxBytesGetter := b.r.ToValue(func(call goja.FunctionCall) goja.Value {
		return b.r.ToValue(b.inspectMaxBytesValue)
	})

	inspectMaxBytesSetter := b.r.ToValue(func(call goja.FunctionCall) goja.Value {
		newValue := call.Argument(0)

		// 类型验证：必须是 number
		if goja.IsUndefined(newValue) || goja.IsNull(newValue) {
			panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType,
				`The "INSPECT_MAX_BYTES" argument must be of type number. Received `+newValue.String()))
		}

		// 检查是否为数字类型
		exported := newValue.Export()
		var numValue float64
		switch v := exported.(type) {
		case int64:
			numValue = float64(v)
		case int:
			numValue = float64(v)
		case float64:
			numValue = v
		case float32:
			numValue = float64(v)
		default:
			// 非数字类型抛出 TypeError
			typeName := "unknown"
			if exported == nil {
				typeName = "undefined"
			} else {
				typeName = reflect.TypeOf(exported).String()
			}
			panic(errors.NewTypeError(b.r, errors.ErrCodeInvalidArgType,
				`The "INSPECT_MAX_BYTES" argument must be of type number. Received type `+typeName))
		}

		// 范围验证：必须 >= 0
		if math.IsNaN(numValue) {
			panic(errors.NewRangeError(b.r, errors.ErrCodeOutOfRange,
				`The value of "INSPECT_MAX_BYTES" is out of range. It must be >= 0. Received NaN`))
		}

		if numValue < 0 {
			panic(errors.NewRangeError(b.r, errors.ErrCodeOutOfRange,
				fmt.Sprintf(`The value of "INSPECT_MAX_BYTES" is out of range. It must be >= 0. Received %v`, numValue)))
		}

		// 更新值（保留浮点数，与 Node.js 对齐）
		b.inspectMaxBytesValue = numValue
		return goja.Undefined()
	})

	exports.DefineAccessorProperty(
		"INSPECT_MAX_BYTES",
		inspectMaxBytesGetter,
		inspectMaxBytesSetter,
		goja.FLAG_FALSE, // configurable
		goja.FLAG_TRUE,  // enumerable
	)

	// 在 exports 上也存储 API 实例引用（用于 inspect 方法访问）
	exports.DefineDataPropertySymbol(symApi, runtime.ToValue(b), goja.FLAG_FALSE, goja.FLAG_FALSE, goja.FLAG_FALSE)

	// 导出 atob 和 btoa 函数（Node.js v25 兼容）
	atobFunc := b.r.ToValue(b.atob)
	if atobObj, ok := atobFunc.(*goja.Object); ok {
		atobObj.DefineDataProperty("length", b.r.ToValue(1), 0, 0, 0)
		atobObj.DefineDataProperty("name", b.r.ToValue("atob"), 0, 0, 0)
	}
	exports.Set("atob", atobFunc)

	btoaFunc := b.r.ToValue(b.btoa)
	if btoaObj, ok := btoaFunc.(*goja.Object); ok {
		btoaObj.DefineDataProperty("length", b.r.ToValue(1), 0, 0, 0)
		btoaObj.DefineDataProperty("name", b.r.ToValue("btoa"), 0, 0, 0)
	}
	exports.Set("btoa", btoaFunc)
}

// atob - ASCII 到二进制 (Base64 解码) - Web 标准实现
func (b *Buffer) atob(call goja.FunctionCall) goja.Value {
	if len(call.Arguments) == 0 {
		panic(b.r.NewTypeError("atob: At least 1 argument required"))
	}

	arg := call.Arguments[0]

	// 检查是否为 Symbol 类型 - 直接检查类型而不是调用转换方法
	if symbol, ok := arg.(*goja.Symbol); ok {
		_ = symbol // 避免未使用变量警告
		panic(b.r.NewTypeError("Cannot convert a Symbol value to a string"))
	}

	// 也检查对象包装的 Symbol
	if obj, ok := arg.(*goja.Object); ok {
		if exported := obj.Export(); exported != nil {
			if _, ok := exported.(*goja.Symbol); ok {
				panic(b.r.NewTypeError("Cannot convert a Symbol value to a string"))
			}
		}
	}

	input := arg.String()

	// 实现符合 Web 标准的 atob 函数
	decoded, err := b.webAtob(input)
	if err != nil {
		// 根据错误类型创建合适的错误消息
		if err.Error() == "character error" {
			panic(b.r.NewGoError(stderrors.New("Invalid character")))
		} else {
			panic(b.r.NewGoError(stderrors.New("The string to be decoded is not correctly encoded.")))
		}
	}
	return b.r.ToValue(decoded)
}

// btoa - 二进制到 ASCII (Base64 编码)
func (b *Buffer) btoa(call goja.FunctionCall) goja.Value {
	if len(call.Arguments) == 0 {
		panic(b.r.NewTypeError("btoa: At least 1 argument required"))
	}

	arg := call.Arguments[0]

	// 检查是否为 Symbol 类型
	if symbol, ok := arg.(*goja.Symbol); ok {
		_ = symbol // 避免未使用变量警告
		panic(b.r.NewTypeError("Cannot convert a Symbol value to a string"))
	}

	// 也检查对象包装的 Symbol
	if obj, ok := arg.(*goja.Object); ok {
		if exported := obj.Export(); exported != nil {
			if _, ok := exported.(*goja.Symbol); ok {
				panic(b.r.NewTypeError("Cannot convert a Symbol value to a string"))
			}
		}
	}

	input := arg.String()

	// 将字符串转换为字节数组 - 每个字符作为一个字节处理（Latin-1）
	bytes := make([]byte, 0, len(input))
	for _, r := range input {
		if r > 255 {
			// 创建 InvalidCharacterError
			err := b.r.NewGoError(stderrors.New("InvalidCharacterError The string to be encoded contains characters outside of the Latin1 range."))
			err.Set("name", b.r.ToValue("InvalidCharacterError"))
			panic(err)
		}
		bytes = append(bytes, byte(r))
	}

	encoded := base64.StdEncoding.EncodeToString(bytes)
	return b.r.ToValue(encoded)
}

// webAtob 实现符合 Web 标准的 atob 函数
func (b *Buffer) webAtob(input string) (string, error) {
	// 1. 如果输入为空字符串，返回空字符串
	if input == "" {
		return "", nil
	}

	// 2. 移除所有空白字符 (space, tab, newline, form feed, carriage return)
	cleaned := b.removeWhitespace(input)

	// 3. 先验证所有字符都是有效的 Base64 字符（优先检查）
	if !b.isValidBase64String(cleaned) {
		return "", stderrors.New("character error")
	}

	// 4. 然后验证字符串长度是否符合 Base64 规则
	if len(cleaned)%4 == 1 {
		return "", stderrors.New("encoding error")
	}

	// 5. 标准化填充
	normalized := b.normalizePadding(cleaned)

	// 6. 使用标准 Base64 解码
	decoded, err := base64.StdEncoding.DecodeString(normalized)
	if err != nil {
		return "", stderrors.New("invalid base64 string")
	}

	// 按照 Web 标准，将每个字节作为 Latin-1 字符处理
	// 而不是作为 UTF-8 字符串处理
	result := make([]rune, len(decoded))
	for i, b := range decoded {
		result[i] = rune(b)
	}
	return string(result), nil
}

// removeWhitespace 移除字符串中的所有 ASCII 空白字符
func (b *Buffer) removeWhitespace(s string) string {
	result := make([]rune, 0, len(s))
	for _, r := range s {
		if r != ' ' && r != '\t' && r != '\n' && r != '\f' && r != '\r' {
			result = append(result, r)
		}
	}
	return string(result)
}

// isValidBase64String 检查字符串是否只包含有效的 Base64 字符
func (b *Buffer) isValidBase64String(s string) bool {
	const base64Chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

	// 创建有效的 Base64 字符集（不包括填充符）
	validChars := make(map[rune]bool, 64)
	for _, r := range base64Chars {
		validChars[r] = true
	}

	// 查找第一个填充符位置
	firstPadding := strings.IndexByte(s, '=')

	if firstPadding == -1 {
		// 没有填充字符，检查所有字符是否有效
		for _, r := range s {
			if !validChars[r] {
				return false
			}
		}
		return true
	}

	// 有填充字符的情况
	// 1. 检查填充符之前的字符是否都是有效的 Base64 字符
	for i := 0; i < firstPadding; i++ {
		if !validChars[rune(s[i])] {
			return false
		}
	}

	// 2. 填充字符只能出现在末尾
	for i := firstPadding; i < len(s); i++ {
		if s[i] != '=' {
			return false
		}
	}

	// 3. 检查填充数量 (最多2个)
	paddingCount := len(s) - firstPadding
	if paddingCount > 2 {
		return false
	}

	// 4. 特殊情况：只有填充符是无效的
	if firstPadding == 0 {
		return false
	}

	// 5. 检查长度是否符合 Base64 规则
	if len(s)%4 != 0 {
		return false
	}

	return true
}

// isValidPadding 检查填充字符(=)的位置是否符合 Base64 规则
func (b *Buffer) isValidPadding(s string) bool {
	// 查找第一个 = 的位置
	firstPadding := -1
	for i, r := range s {
		if r == '=' {
			firstPadding = i
			break
		}
	}

	if firstPadding == -1 {
		// 没有填充字符，这是允许的
		return true
	}

	// 填充字符只能出现在末尾
	for i := firstPadding; i < len(s); i++ {
		if s[i] != '=' {
			return false
		}
	}

	// 检查填充数量 (最多2个)
	paddingCount := len(s) - firstPadding
	return paddingCount <= 2
}

// normalizePadding 标准化 Base64 填充
func (b *Buffer) normalizePadding(s string) string {
	// 如果字符串长度已经是4的倍数，直接返回
	if len(s)%4 == 0 {
		return s
	}

	// 添加必要的填充字符
	paddingNeeded := 4 - (len(s) % 4)
	return s + strings.Repeat("=", paddingNeeded)
}

func init() {
	require.RegisterCoreModule(ModuleName, Require)
}
