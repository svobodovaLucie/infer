(window.webpackJsonp=window.webpackJsonp||[]).push([[52],{188:function(e,n,t){"use strict";t.r(n),t.d(n,"frontMatter",(function(){return i})),t.d(n,"metadata",(function(){return u})),t.d(n,"rightToc",(function(){return f})),t.d(n,"default",(function(){return p}));var r=t(2),a=t(9),o=(t(0),t(298)),c=t(299),i={id:"man-infer",title:"infer"},u={id:"man-infer",isDocsHomePage:!1,title:"infer",source:"@site/docs/man-infer.md",permalink:"/docs/next/man-infer",version:"next",sidebar:"docs",previous:{title:"Advanced usage",permalink:"/docs/next/advanced-features"},next:{title:"infer analyze",permalink:"/docs/next/man-infer-analyze"},latestVersionMainDocPermalink:"/docs/getting-started"},f=[],l={rightToc:f};function p(e){var n=e.components,t=Object(a.a)(e,["components"]);return Object(o.b)("wrapper",Object(r.a)({},l,t,{components:n,mdxType:"MDXLayout"}),Object(o.b)(c.a,{url:"/man/next/infer.1.html",mdxType:"HtmlWrap"}))}p.isMDXComponent=!0},298:function(e,n,t){"use strict";t.d(n,"a",(function(){return p})),t.d(n,"b",(function(){return d}));var r=t(0),a=t.n(r);function o(e,n,t){return n in e?Object.defineProperty(e,n,{value:t,enumerable:!0,configurable:!0,writable:!0}):e[n]=t,e}function c(e,n){var t=Object.keys(e);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);n&&(r=r.filter((function(n){return Object.getOwnPropertyDescriptor(e,n).enumerable}))),t.push.apply(t,r)}return t}function i(e){for(var n=1;n<arguments.length;n++){var t=null!=arguments[n]?arguments[n]:{};n%2?c(Object(t),!0).forEach((function(n){o(e,n,t[n])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(t)):c(Object(t)).forEach((function(n){Object.defineProperty(e,n,Object.getOwnPropertyDescriptor(t,n))}))}return e}function u(e,n){if(null==e)return{};var t,r,a=function(e,n){if(null==e)return{};var t,r,a={},o=Object.keys(e);for(r=0;r<o.length;r++)t=o[r],n.indexOf(t)>=0||(a[t]=e[t]);return a}(e,n);if(Object.getOwnPropertySymbols){var o=Object.getOwnPropertySymbols(e);for(r=0;r<o.length;r++)t=o[r],n.indexOf(t)>=0||Object.prototype.propertyIsEnumerable.call(e,t)&&(a[t]=e[t])}return a}var f=a.a.createContext({}),l=function(e){var n=a.a.useContext(f),t=n;return e&&(t="function"==typeof e?e(n):i(i({},n),e)),t},p=function(e){var n=l(e.components);return a.a.createElement(f.Provider,{value:n},e.children)},s={inlineCode:"code",wrapper:function(e){var n=e.children;return a.a.createElement(a.a.Fragment,{},n)}},m=a.a.forwardRef((function(e,n){var t=e.components,r=e.mdxType,o=e.originalType,c=e.parentName,f=u(e,["components","mdxType","originalType","parentName"]),p=l(t),m=r,d=p["".concat(c,".").concat(m)]||p[m]||s[m]||o;return t?a.a.createElement(d,i(i({ref:n},f),{},{components:t})):a.a.createElement(d,i({ref:n},f))}));function d(e,n){var t=arguments,r=n&&n.mdxType;if("string"==typeof e||r){var o=t.length,c=new Array(o);c[0]=m;var i={};for(var u in n)hasOwnProperty.call(n,u)&&(i[u]=n[u]);i.originalType=e,i.mdxType="string"==typeof e?e:r,c[1]=i;for(var f=2;f<o;f++)c[f]=t[f];return a.a.createElement.apply(null,c)}return a.a.createElement.apply(null,t)}m.displayName="MDXCreateElement"},299:function(e,n,t){"use strict";t.d(n,"a",(function(){return o}));var r=t(0),a=t.n(r);function o(e){var n=e.url,t=Object(r.useState)({__html:""}),o=t[0],c=t[1];return Object(r.useEffect)((function(){fetch(n).then((function(e){return e.text()})).then((function(e){return c({__html:e})}))}),[n]),a.a.createElement("div",{dangerouslySetInnerHTML:o})}}}]);