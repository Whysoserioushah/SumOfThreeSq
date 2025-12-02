import VersoBlog

import Blog

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          <link rel="stylesheet" href="/static/style.css"/>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            {{ if (← currentPath).isEmpty then .empty else
              {{ <a class="logo" href="/"><h1>"Sum of Three Squares"</h1></a> }} }}
            -- {{ ← topNav }}
            </div>
          </header>
          <main>
            <div class="wrap">
              {{← param "content" }}
            </div>
          </main>
        </body>
      </html>
    }}
  }
  |>.override #[] {
    template := do
      return {{<div class="frontpage">{{← param "content"}}</div>}},
    params := id
  }


def blog : Site := site Blog.About /
  static "static" ← "static_files"
  "prereq" Blog.Prerequists
  -- "about" Blog.About
  -- "blog" Blog.Posts with
  --   Blog.Posts.Comparison
  --   Blog.Posts.FibIter
  --   Blog.Posts.Welcome
  --   Blog.Posts.FirstPost


def main := blogMain theme blog (options := ["--output", "../docs"])

run_meta do
  let opt ← Lean.getOptions
  if Lean.Elab.inServer.get opt then _ ← main
