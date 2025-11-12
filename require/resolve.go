package require

import (
	"encoding/json"
	"errors"
	"path/filepath"
	"runtime"
	"strings"

	js "github.com/dop251/goja"
)

const NodePrefix = "node:"

func (r *RequireModule) resolvePath(base, name string) string {
	if r.r.pathResolver != nil {
		return r.r.pathResolver(base, name)
	}
	return DefaultPathResolver(base, name)
}

// NodeJS module search algorithm described by
// https://nodejs.org/api/modules.html#modules_all_together
func (r *RequireModule) resolve(modpath string) (module *js.Object, err error) {
	var start string
	err = nil
	if !filepath.IsAbs(modpath) {
		start = r.getCurrentModulePath()
	}

	p := r.resolvePath(start, modpath)
	if isFileOrDirectoryPath(modpath) {
		if module = r.modules[p]; module != nil {
			if cached := r.getCachedModule(p); cached != nil {
				if module != cached {
					r.modules[p] = cached
				}
				return cached, nil
			}
			delete(r.modules, p)
			module = nil
		}
		module, err = r.loadAsFileOrDirectory(p)
		if err == nil && module != nil {
			r.modules[p] = module
		}
	} else {
		module, err = r.loadNative(modpath)
		if err == nil {
			return
		} else {
			if err == InvalidModuleError {
				err = nil
			} else {
				return
			}
		}
		if module = r.nodeModules[p]; module != nil {
			if cached := r.getCachedModule(p); cached != nil {
				if module != cached {
					r.nodeModules[p] = cached
				}
				return cached, nil
			}
			delete(r.nodeModules, p)
			module = nil
		}
		module, err = r.loadNodeModules(modpath, start)
		if err == nil && module != nil {
			r.nodeModules[p] = module
		}
	}

	if module == nil && err == nil {
		err = InvalidModuleError
	}
	return
}

func (r *RequireModule) loadNative(path string) (*js.Object, error) {
	if module := r.modules[path]; module != nil {
		if cached := r.getCachedModule(path); cached != nil {
			if module != cached {
				r.modules[path] = cached
			}
			return cached, nil
		}
		delete(r.modules, path)
	}

	var ldr ModuleLoader
	if ldr = r.r.native[path]; ldr == nil {
		ldr = native[path]
	}

	var isBuiltIn, withPrefix bool
	if ldr == nil {
		ldr = builtin[path]
		if ldr == nil && strings.HasPrefix(path, NodePrefix) {
			ldr = builtin[path[len(NodePrefix):]]
			if ldr == nil {
				return nil, NoSuchBuiltInModuleError
			}
			withPrefix = true
		}
		isBuiltIn = true
	}

	if ldr != nil {
		module := r.createModuleObject(path)
		r.modules[path] = module
		r.addToCache(path, module)
		if isBuiltIn {
			if withPrefix {
				r.modules[path[len(NodePrefix):]] = module
				r.addToCache(path[len(NodePrefix):], module)
			} else {
				if !strings.HasPrefix(path, NodePrefix) {
					r.modules[NodePrefix+path] = module
					r.addToCache(NodePrefix+path, module)
				}
			}
		}
		ldr(r.runtime, module)
		module.Set("loaded", r.runtime.ToValue(true))
		return module, nil
	}

	return nil, InvalidModuleError
}

func (r *RequireModule) loadAsFileOrDirectory(path string) (module *js.Object, err error) {
	if module, err = r.loadAsFile(path); module != nil || err != nil {
		return
	}

	return r.loadAsDirectory(path)
}

func (r *RequireModule) loadAsFile(path string) (module *js.Object, err error) {
	if module, err = r.loadModule(path); module != nil || err != nil {
		return
	}

	p := path + ".js"
	if module, err = r.loadModule(p); module != nil || err != nil {
		return
	}

	p = path + ".json"
	return r.loadModule(p)
}

func (r *RequireModule) loadIndex(modpath string) (module *js.Object, err error) {
	p := r.resolvePath(modpath, "index.js")
	if module, err = r.loadModule(p); module != nil || err != nil {
		return
	}

	p = r.resolvePath(modpath, "index.json")
	return r.loadModule(p)
}

func (r *RequireModule) loadAsDirectory(modpath string) (module *js.Object, err error) {
	p := r.resolvePath(modpath, "package.json")
	buf, err := r.r.getSource(p)
	if err != nil {
		return r.loadIndex(modpath)
	}
	var pkg struct {
		Main string
	}
	err = json.Unmarshal(buf, &pkg)
	if err != nil || len(pkg.Main) == 0 {
		return r.loadIndex(modpath)
	}

	m := r.resolvePath(modpath, pkg.Main)
	if module, err = r.loadAsFile(m); module != nil || err != nil {
		return
	}

	return r.loadIndex(m)
}

func (r *RequireModule) loadNodeModule(modpath, start string) (*js.Object, error) {
	return r.loadAsFileOrDirectory(r.resolvePath(start, modpath))
}

func (r *RequireModule) loadNodeModules(modpath, start string) (module *js.Object, err error) {
	for _, dir := range r.r.globalFolders {
		if module, err = r.loadNodeModule(modpath, dir); module != nil || err != nil {
			return
		}
	}
	for {
		var p string
		if filepath.Base(start) != "node_modules" {
			p = filepath.Join(start, "node_modules")
		} else {
			p = start
		}
		if module, err = r.loadNodeModule(modpath, p); module != nil || err != nil {
			return
		}
		if start == ".." { // Dir('..') is '.'
			break
		}
		parent := filepath.Dir(start)
		if parent == start {
			break
		}
		start = parent
	}

	return
}

func (r *RequireModule) getCurrentModulePath() string {
	var buf [2]js.StackFrame
	frames := r.runtime.CaptureCallStack(2, buf[:0])
	if len(frames) < 2 {
		return "."
	}
	return filepath.Dir(frames[1].SrcName())
}

func (r *RequireModule) createModuleObject(path string) *js.Object {
	module := r.runtime.NewObject()
	module.Set("id", r.runtime.ToValue(path))
	module.Set("filename", r.runtime.ToValue(path))
	module.Set("loaded", r.runtime.ToValue(false))
	module.Set("parent", js.Undefined())
	module.Set("children", r.runtime.NewArray())
	module.Set("exports", r.runtime.NewObject())
	return module
}

func (r *RequireModule) loadModule(path string) (*js.Object, error) {
	if module := r.modules[path]; module != nil {
		if cached := r.getCachedModule(path); cached != nil {
			if module != cached {
				r.modules[path] = cached
			}
			return cached, nil
		}
		delete(r.modules, path)
	}
	module := r.createModuleObject(path)
	r.modules[path] = module
	r.addToCache(path, module)
	err := r.loadModuleFile(path, module)
	if err != nil {
		delete(r.modules, path)
		r.removeFromCache(path)
		if errors.Is(err, ModuleFileDoesNotExistError) {
			err = nil
		}
		return nil, err
	}
	module.Set("loaded", r.runtime.ToValue(true))
	return module, nil
}

func (r *RequireModule) loadModuleFile(path string, jsModule *js.Object) error {

	prg, err := r.r.getCompiledSource(path)

	if err != nil {
		return err
	}

	f, err := r.runtime.RunProgram(prg)
	if err != nil {
		return err
	}

	if call, ok := js.AssertFunction(f); ok {
		jsExports := jsModule.Get("exports")
		jsRequire := r.runtime.Get("require")

		// Run the module source, with "jsExports" as "this",
		// "jsExports" as the "exports" variable, "jsRequire"
		// as the "require" variable and "jsModule" as the
		// "module" variable (Nodejs capable).
		_, err = call(jsExports, jsExports, jsRequire, jsModule, r.runtime.ToValue(path), r.runtime.ToValue(filepath.Dir(path)))
		if err != nil {
			return err
		}
	} else {
		return InvalidModuleError
	}

	return nil
}

func isFileOrDirectoryPath(path string) bool {
	result := path == "." || path == ".." ||
		strings.HasPrefix(path, "/") ||
		strings.HasPrefix(path, "./") ||
		strings.HasPrefix(path, "../")

	if runtime.GOOS == "windows" {
		result = result ||
			strings.HasPrefix(path, `.\`) ||
			strings.HasPrefix(path, `..\`) ||
			filepath.IsAbs(path)
	}

	return result
}
