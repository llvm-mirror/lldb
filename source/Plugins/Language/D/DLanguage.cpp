//===-- DLanguage.cpp
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "DLanguage.h"

#include "lldb/Core/PluginManager.h"
#include "lldb/Utility/ConstString.h"

#include <dlfcn.h>

using namespace lldb;
using namespace lldb_private;

char* lldbd_demangle(size_t length, const char* mangled);
void d_initialize();

// TODO:MOVE
struct SharedLib{
  void* handle;
  const char* libraryFile;
  int flagDefault = RTLD_LOCAL | RTLD_LAZY;
  SharedLib(){
  }

  ~SharedLib(){
    release();
  }

  // Return true of `dlopen` succeeded
  bool open(const char* libraryFile, int flag)
  {
      release();
      this->libraryFile = libraryFile;
      handle = dlopen(libraryFile, flag);
      if (handle)
          return true;
      return false;
  }
  
  void release()
  {
      // if(handle) seems needed: https://stackoverflow.com/questions/11412943is-it-safe-to-call-dlclosenull
      if (handle)
          dlclose(handle);
  }

  template<typename Fun>
  Fun* getFun(const char*symbol)
  {
      assert(handle);
      return reinterpret_cast<Fun*>(dlsym(handle, symbol));
  }
};

void DLanguage::Initialize() {
  PluginManager::RegisterPlugin(GetPluginNameStatic(), "D Language",
                                CreateInstance);
}

void DLanguage::Terminate() {
  PluginManager::UnregisterPlugin(CreateInstance);
}

lldb_private::ConstString DLanguage::GetPluginNameStatic() {
  static ConstString g_name("D");
  return g_name;
}

//------------------------------------------------------------------
// PluginInterface protocol
//------------------------------------------------------------------
lldb_private::ConstString DLanguage::GetPluginName() {
  return GetPluginNameStatic();
}

uint32_t DLanguage::GetPluginVersion() { return 1; }

//------------------------------------------------------------------
// Static Functions
//------------------------------------------------------------------
Language *DLanguage::CreateInstance(lldb::LanguageType language) {
  switch (language) {
  case lldb::eLanguageTypeD:
    return new DLanguage();
  default:
    return nullptr;
  }
}

char* DLanguage::demangle(const ConstString &mangled) {
  auto len=mangled.GetLength();
  auto s=mangled.GetCString();
  // IMPROVE
  static auto fun=[]() -> decltype(lldbd_demangle)*{
    auto lib2=new SharedLib();
    // TODO: so vs dylib
    auto file="liblldbdplugin.dylib";
    if(!lib2->open(file, lib2->flagDefault)){
      return nullptr;
    }

    auto fun0=lib2->getFun<decltype(d_initialize)>("d_initialize");
    (*fun0)();

    auto fun=lib2->getFun<decltype(lldbd_demangle)>("lldbd_demangle");
    assert(fun);
    return fun;
  }();
  if(!fun) return nullptr;
  return (*fun)(len, s);
}

bool DLanguage::IsDMangledName(const char *name) {
  if (name == nullptr)
    return false;
  return (name[0] != '\0' && name[0] == '_' && name[1] == 'D');
}
