
import time
import threading
import json
import os

from email.quoprimime import unquote
from http.server import BaseHTTPRequestHandler, HTTPServer
from socketserver import ThreadingMixIn
from re import A, S
import re
from tkinter import E
from unicodedata import category
from urllib.parse import parse_qs, urlparse, quote, unquote


from selenium import webdriver
from bs4 import BeautifulSoup
from urllib.request import urlopen, Request
from datetime import datetime, timedelta
import requests

from abc import *

from wordcloud import WordCloud
from konlpy.tag import Twitter
from PIL import Image
import numpy as np
from collections import Counter

from gensim.models.doc2vec import TaggedDocument
from tqdm import tqdm
import re

from gensim.models import TfidfModel,doc2vec, Doc2Vec
from gensim.corpora import Dictionary
from konlpy.tag import Mecab, Okt
import sys

port = int(sys.argv[1]) if len(sys.argv)>1 else 80
train = bool(sys.argv[2]) if len(sys.argv)>2 else False
test = False

webdriver_path="D:/school/객프/chromedriver.exe"
jsonpath="D:/school/객프/crawler.json"

class Crawler:
    def __init__(self, comment_wait_time=5, comment_delay_time=0.1, webdriver_path="D:/school/객프/chromedriver.exe", jsonpath="./crawler.json"):
        self._arts=[] # Stores structured article data
        self.idind=0 # Using it for indexing articles
        self.wait_time=comment_wait_time
        self.delay_time=comment_delay_time
        self.jsonpath=jsonpath
        self.webdriver_options = webdriver.ChromeOptions()
        self.webdriver_options._experimental_options['excludeSwitches']=['enable-logging']
        self.webdriver_options.add_argument('headless')
        self.webdriver_path=webdriver_path
        if os.path.isfile(jsonpath): #if there is a file named
            self.Load() #load
        self.category=self.GetCategoryItems()
        self.DriverLoad()
        self.DriverQuit()
    def Save(self, test=None):
        # Save data into json form
        path="./test.json" if test== True else self.jsonpath
        jstr=json.dumps({"idind":self.idind, "arts":self._arts}) #save udind, arts to json format
        with open(path, "w") as myfile:
            myfile.write(jstr)
        print("Saved!")
    def Load(self, test=None): #changed
        # Load data from json file
        path="./test.json" if test== True else self.jsonpath
        if test:
            self.Save(test=True)
        with open(path, "r") as myfile: 
            tmp=json.loads(myfile.read())
            self.idind=tmp["idind"]
            self._arts=tmp["arts"]
        print(f"{len(self._arts)} Loaded!")
    def CheckDuplicated(self):
        urls=[i["title"] for i in self._arts]
        print(Counter(urls).most_common(10))
        #for i in idl:
    def GetAndRegister(self, url): #Changed
        #Save structured data of given article from url
        if url in [i["url"] for i in self._arts]:
            print("Duplicated, exit")
            return
        (title, img, article, date, topics) = self.CrawlArticle(url) #Crawl title, images, article contents
        if title==None or article==None or date==None:
            print("Possible invalidation of url, exit")
            return
        # Date format: 2022-05-01 10:29:05
        # date=dt.strptime(date, "%Y-%m-%d %H:%M:%S")
        a=urlparse(url)
        rep=a.path.split("/")
        curl=f"{a.scheme}://{a.netloc}/article/comment/{rep[2]}/{rep[3]}"
        comments_raw = self.GetNewsComments(curl, self.wait_time, self.delay_time) #Crawl comments
        comments=[]
        for i in comments_raw:
            #id, date, comment, likes, dislikes
            comments.append({"name":i[0], "date":i[1], "content":i[2], "likes":int(i[3]), "dislikes":int(i[4])})
        self._arts.append({"id":self.idind, "title":title, "date":date, "url":url, "topics":topics, "article":{"img":img, "content":article}, "comments":comments,"keyword":[]})
        self.idind+=1
    def CrawlValidate(self, n=30, count=50):
        c=Counter()
        for i in self._arts:
            c[i["date"].split(" ")[0]]+=1
        c=sorted(c.items())
        for k,v in c:
            if v<n:
                num=count-v
                date=datetime.strptime(k, "%Y-%m-%d")
                day=date.strftime("%Y%m%d")
                print(f"Processing {day} of {num} (current:{v})")
                self.CrawlPopularByDate(day,num)
                self.Save()
    def CrawlPopularByDate(self, date="20220424", range=50):
        #Crawl all articles by the day
        try:
            self.DriverLoad()
            crawlList=self.GetPopularArticlesByDay(date)
            nr=(range if range<len(crawlList) else len(crawlList)) if range!=-1 else len(crawlList)
            print(f"Processing {nr}/{len(crawlList)} data from {date}...")
            for i,d in enumerate(crawlList[:nr]):
                try:
                    self.GetAndRegister(d["href"])
                    print(i, d["title"])
                except Exception as e:
                    print("error occured while loop --- ")
                    print(e)
            self.DriverQuit()
            print("Done!")
        except Exception as e:
            print("error occured while whole")
            print(e)
    def CrawlGoGO(self, start=0,end=0,num=100):
        a=datetime.today()-timedelta(days=start)
        for i in range(end):
            day=(a-timedelta(days=i)).strftime("%Y%m%d")
            print(day, " Day Processing")
            self.CrawlPopularByDate(day,num)
            self.Save()
    def GetItem(self, id):
        # Get item of given id
        for i in self._arts:
            if i["id"]==id:
                return i
    def GetComments(self, id):
        # Get comments of given article by id
        return self.GetItem(id)["comments"]
    def GetTitle(self, id):
        # Get comments of given article by id
        return self.GetItem(id)["title"]
    def GetArticle(self, id):
        # Get comments of given article by id
        return self.GetItem(id)["article"]
    def GetDate(self, id):
        # Get date of given article by id
        return self.GetItem(id)["date"]
    def GetTopics(self, id):
        return self.GetItem(id)["topics"]
    # Usage of basic methods
    def GetHighestLC(self, id):
        # Get a comment having highest likes
        work=self.GetComments(id)
        maxl=-1
        maxc={}
        for j in work:
            if(j["likes"]>maxl):
                maxl=j["likes"]
                maxc=j
        return maxc
    def GetSimilarLC(self, id):
        # Get a comment having ratio close to 1:1 likes and dislikes
        work=self.GetComments(id)
        maxratio=0
        maxc={}
        highc=self.GetHighestLC(id)
        for j in work:
            if j["likes"] is 0 or j["dislikes"] is 0:
                continue
            h=j["likes"] if j["likes"]>j["dislikes"] else j["dislikes"]
            l=j["likes"] if j["likes"]<j["dislikes"] else j["dislikes"]
            ratio=(l/h)*(l+h)
            if ratio>maxratio and highc != j:
                maxratio=ratio
                maxc=j
        return maxc
    def GetSummary(self, id):
        # Get replaced data for displaying summary of article
        work=self.GetArticle(id)["content"]
        return work.replace("\n"," ")
    def GetThumbnail(self, id):
        # Get first image of article
        return self.GetArticle(id)["img"][0]["src"] if len(self.GetArticle(id)["img"])>0 else ""
    def GetRecommendFormat(self, id):
        # Get recommend article formated data (thumbnail, title, desc, liked comment, ratio comment)
        thumb=self.GetThumbnail(id)
        return {"thumb":thumb if thumb!=None else "", "title":self.GetTitle(id), "desc":self.GetSummary(id), "liked":self.GetHighestLC(id), "sameratio":self.GetSimilarLC(id), "id":id}
    def GetFilteredArticles(self, ids :list, num=15, order="latest"):
        #Return article's thumbnails and desc, titles and urls of given ids, by specified order ("latest", "popular") 
        #{title:"blah", desc:"blah", thumbnail:"blah", date:"blah", id:1}
        res=[]
        for i in ids:
            item=self.GetItem(i)
            res.append({"title":item['title'], "date":item['date'], "desc":self.GetSummary(i), "thumb":self.GetThumbnail(i), "id":i, "cn":len(self.GetComments(i))})
        if order=="latest":
            res=sorted(res, key=lambda x: datetime.strptime(x["date"], "%Y-%m-%d %H:%M:%S").timestamp(),reverse=True)
        elif order=="popular":
            res=sorted(res, key=lambda x: x["cn"],reverse=True)
        else:
            raise
        n=len(res) if num>len(res) else num
        return res[:n]
    def GetCategoryItems(self):
        category={}
        for i in self._arts:
            for j in i["topics"]:
                if not j in category.keys():
                    category.update({j:[]})
                if not i["id"] in category.get(j):
                    category.get(j).append(i["id"])
        return category
    def CategoryView(self,ct):
        de=unquote(ct)
        pol=self.category.get(de, None)
        if pol is None:
            return None
        latest=self.GetFilteredArticles(pol, num=20, order="latest")
        popular=self.GetFilteredArticles(pol, num=20, order="popular")
        return {"keyword":ct, "latest":latest, "popular":popular}
    def MainView(self):
        #Return main components
        m={}
        for k,v in self.category.items():
            m.update({k:self.GetFilteredArticles(v, num=20,order="latest")})
        return {"category":m}
    def GetCategoryFiltered(self, category='정치', num=15, order="popular"):
        pass
    def DriverLoad(self):
        #For crawling efficiency, load chromedriver globally
        self.driver=webdriver.Chrome(self.webdriver_path,options=self.webdriver_options)
    def DriverQuit(self):
        #Shutdown global chromedriver
        self.driver.quit()
    def GetNewsComments(self, url, wait_time=5, delay_time=0.1):
        # (크롬)드라이버가 요소를 찾는데에 최대 wait_time 초까지 기다림 (기본값은 5초)
        driver=self.driver
        driver.implicitly_wait(wait_time)

        # url 주소를 가져와서 접속
        driver.get(url)

        # 더보기가 안뜰 때 까지 계속 클릭
        while True:

            # 예외처리 구문 - 더보기 광클하다가 없어서 에러 뜨면 while문을 나감(break)
            try:
                more = driver.find_element_by_css_selector('a.u_cbox_btn_more')
                more.click()
                time.sleep(delay_time)

            except:
                break

        # 본격적인 크롤링 타임
        
        # 1)작성자
        # selenium으로 작성자 포함된 태그 모두 수집
        nicknames = driver.find_elements_by_css_selector('span.u_cbox_nick')
        # 리스트에 텍스트만 담기 (리스트 컴프리핸션 문법)
        list_nicknames = [nick.text for nick in nicknames]

        # 2)댓글 시간
        # selenium으로 댓글 날짜 포함된 태그 모두 수집
        datetimes = driver.find_elements_by_css_selector('span.u_cbox_date')
        # 리스트에 텍스트만 담기
        list_datetimes = [datetime.text for datetime in datetimes]

        # 3)댓글 내용
        # selenium으로 댓글내용 포함된 태그 모두 수집
        contents = driver.find_elements_by_css_selector('span.u_cbox_contents')
        # 리스트에 텍스트만 담기
        list_contents = [content.text for content in contents]

        # 4) 좋아요 추출
        likes = driver.find_elements_by_css_selector('em.u_cbox_cnt_recomm')
        # 속도 개선
        # likes = soup.select('em.u_cbox_cnt_recomm')
        # 리스트에 담기

        list_likes=list()
        for like in likes:
            list_likes.append(like.text)

        # 5) 싫어요 추출
        disLikes=driver.find_elements_by_css_selector('em.u_cbox_cnt_unrecomm')
        # 속도 개선
        # disLikes = soup.select('em.u_cbox_cnt_unrecomm')
        list_disLikes=list()
        for disLike in disLikes:
            list_disLikes.append(disLike.text)

        # 4)작성자, 댓글 시간, 내용을 셋트로 취합
        list_sum = list(zip(list_nicknames, list_datetimes, list_contents,list_likes,list_disLikes))
        # 함수를 종료하며 list_sum을 결과물로 제출
        return list_sum

    @staticmethod
    def GetPopularArticlesByDay(date="20220424"):
        # Get Article list to crawl from given day
        # Return : list(dict of title, href)
        url = f'https://news.naver.com/main/ranking/popularDay.naver?date={date}'
        hd={'User-Agent':'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/101.0.4951.41 Safari/537.36'}
        req=Request(url,headers=hd)
        html = urlopen(req).read()
        soup = BeautifulSoup(html, 'html.parser')
        titles_html = soup.select(".rankingnews_list > li > div > a")
        lst=[]
        seen = set()
        for i,d in enumerate(titles_html):
            if not d['href'] in seen:
                seen.add(d['href'])
                lst.append({"title":d.text, "href":d['href']})
        print(f"no duplicated found, as number of {len(seen)}" if (len(seen)==len(lst)) else f"duplicated found, seen-lst= {len(seen)-len(lst)}")
        return lst
    @staticmethod
    def CrawlArticle(url): #changed
        try:
            # Get Article extracted data from given url
            # Return : (title, img(dict), article(string), date, topics)
            hd={'User-Agent':'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/101.0.4951.41 Safari/537.36'}
            req=Request(url,headers=hd)
            html = urlopen(req).read()
            soup = BeautifulSoup(html, 'html.parser')
            title = soup.find(class_='media_end_head_headline').text.strip()
            content = soup.find(id="dic_area")
            date = soup.find(class_="_ARTICLE_DATE_TIME")["data-date-time"]
            tags = soup.find_all(class_="media_end_categorize_item")
            img = []
            topics = []
            article=""
            for i in tags:
                topics.append(i.string)
            for i in content.find_all():
                # For image extraction
                if i.has_attr("class"):
                    if i['class'][0]=="end_photo_org":
                        # If it has image class
                        ti=i.find("img") #find image tags
                        if ti.has_attr("data-src"):
                            img.append({"src":ti["data-src"], "desc":i.text.strip()}) #extract description and image source
            for i in content.find_all(text=True):
                # For text extraction
                if not ((i.parent.has_attr("class") and i.parent["class"][0]=="img_desc")): #if it's not image description
                    article+=i #Add to article
            return (title, img, article, date, topics)
        except Exception as e:
            print(f"Error while crawling article, {e}")
            return (None, None, None, None, None)
    @staticmethod
    def GetSearchedArticles(search, n=5):
        url_list = []
        for page_num in range(1, n):
            url = "https://search.naver.com/search.naver?where=news&sm=tab_pge&query=" + search + "&start=" + str(page_num)
            url_list.append(url)

        # ConnectionError방지
        headers = {'User-Agent':'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/101.0.4951.41 Safari/537.36'}
        news_url = []
        news_title=[]
        for url in url_list:
            # html불러오기
            original_html = requests.get(url, headers=headers)
            html = BeautifulSoup(original_html.text, "html.parser")

            # 검색결과
            base = html.select("div.group_news > ul.list_news > li div.news_area > a")
            articles = html.select("div.group_news > ul.list_news > li div.news_area > div.news_info > div.info_group > a")
            
            # 뉴스기사 URL 가져오기
            for i in articles:
                if not "press" in i["class"]:
                    news_url.append(i.attrs['href'])
            for i in base:
                news_title.append(i.attrs['title'])
        return (news_title,news_url)
    def test(self):
        backup_arts=self._arts
        backup_idind=self.idind
        try:
            self.Save(test=True)
            valid=False
            if os.path.isfile("./test.json"):
                valid=True
            print("Save: "+valid)
        except:
            print("error during Save")

        try:
            self.Load(test=True)
        except:
            print("error during Load")
        
        try:
            t=len(self._arts)
            self.GetAndRegister("https://n.news.naver.com/article/025/0003184626?ntype=RANKING")
            valid=t!=len(self._arts)
            print("GetAndRegister: "+valid)
        except:
            print("error during GetAndRegister")
        
        try:
            print("GetPopularArticlesByDay: ",len(self.GetPopularArticlesByDay("20220501"))>0)
        except:
            print("error during GetPopularArtuclesByDay!!")
        
        try:
            p=len(self._arts)
            self.CrawlGoGO(0,1, num=1)
            valid=len(self._arts)!=p
            print("CrawlGoGO:",valid)
        except:
            print("error during CrawlGoGo!!")
        testimg=[{"src":"https://imgnews.pstatic.net/image/028/2022/05/10/0002589972_001_20220510113501131.jpg?type=w647", "desc":"seok"},{"src":"https://imgnews.pstatic.net/image/028/2022/05/10/0002589972_001_20220510113501131.jpg?type=w647", "desc":"lol"}]

        testcmt=[{"name":"blah", "date":"202205010", "content":"lol", "likes":3, "dislikes":1},{"name":"blah", "date":"202205010", "content":"lol", "likes":3, "dislikes":1}]
        self._arts=[{"id":0, "title":"sampletitle", "date":"20220510", "url":"https://n.news.naver.com/article/028/0002589972", "topics":["test", "test2"], "article":{"img":testimg, "content":"This is content"}, "comments":testcmt,"keyword":[]}]
        #work todo
        try:
            print("GetSearchedArticles:",self.GetItem(0)["id"]==0)
        except:
            print("error during GetSeachedArticles!!")
        try:
            print("GetComments:",len(self.GetComments(0))>0)
        except:
            print("error during GetComments!!")
        try:
            print("GetTitle:",len(self.GetTitle(0))>0)
        except:
            print("error during GetTitle!!")
        try:
            print("GetArticle:",len(self.GetArticle(0))>0)
        except:
            print("error during GetArticle!!")
        try:
            print("GetDate:",len(self.GetDate(0))>0)
        except:
            print("error during GetDate!!")
        try:
            print("GetTopic:",len(self.GetTopics(0))>0)
        except:
            print("error during GetTopcis!!")
        
        try:
            print("GetThumbnail: ",len(self.GetThumbnail(0))>0)
        except:
            print("error during GetThumbnail!!")

        try:
            print("GetSimilarLC: ",len(self.GetSimilarLC(0)["name"])>0)
        except:
            print("error during GetSimilarLC!!")

        try:
            print("GetHighestLC: ",len(self.GetHighestLC(0)["name"])>0)
        except:
            print("error during GetHighest!!")
        try:
            print("GetSummary: ",len(self.GetSummary(0))>0)
        except:
            print("error during GetSummary!!")
        
        try:
            self.DriverLoad()
            self.DriverQuit()
            print("DriverLoad&Quit: True")
        except:
            print("error during driver load")

        try:
            print("GetNewsComments: ",len(self.GetNewsComments("https://n.news.naver.com/article/comment/032/0003145282"))>0)
        except:
            print("error during GetNewsComments!!")

        try:
            print("CrawlPopularByDate: ",len(self.GetPopularArticlesByDay())>0)
        except:
            print("error during CrawlPopularByDate!!")
        try:
            (t, i, a, d, topic)=self.CrawlArticle("https://n.news.naver.com/article/123/0002273845?cds=news_media_pc&type=editn")
            print("CrawlArticle:", (len(t)>0 and len(a)>0 and len(d)>0 and len(topic)>0))
        except:
            print("error during CrawlArticle!!")

        try:
            print("GetSearchedArticles:",len(self.GetSearchedArticles("윤석열")[0])>0)
        except:
            print("error during GetSeachedArticles!!")
        
        self._arts=backup_arts
        self.idind=backup_idind
class abcKeyword(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, crawler :Crawler):
        self.crawler=crawler
        self.categories={} #categories and its article ids
        self.keywords={} #keywords and its
        self.AreaKeywords={}
    @abstractmethod
    def ExtractKeyword(self, x):
        #Extract keywords from all articles using lda and save it to crawler.arts
        pass
    @abstractmethod
    def KeywordView(self, x):
        #Return dyanmic keywords view (dict)
        pass
    @abstractmethod
    def ExtractKeywordsByArea(self, area):
        #Extract keywords from area search (using self.ExtractKeyword)
        pass
    @abstractmethod
    def CategorizeKeywords(self, x):
        #Categorize Keywords by articles and save to self
        pass
    @abstractmethod
    def LatestArticlesByCategory(self, category, range):
        #Return Cateogirze articles in latest order
        pass
    @abstractmethod
    def SimilarArticle(self, id):
        pass
    def GetKeyowrds(self):
        return self.keywords
    def GetAreaKeywords(self, area):
        if area in self.AreaKeywords.keys():
            return self.AreaKeywords["area"]
        else:
            return []
class Keyword(abcKeyword):
    def __init__(self, crawler):
        super().__init__(crawler)
        self.okt=Okt()
        if not train:
            print("Loading Doc2vec..")
            self.model=Doc2Vec.load('dart.doc2vec')
        else:
            print("Loading empty shell..")
            self.model = doc2vec.Doc2Vec(vector_size=300, alpha=0.025, min_alpha=0.025, workers=8, window=8)
        if os.path.isfile("./keywords.json"): #if there is a file named
            self.Load() #load
    def Save(self, path="./keywords.json"):
        jstr=json.dumps({"keywords":self.keywords}) #save udind, arts to json format
        with open(path, "w") as myfile:
            myfile.write(jstr)
        print("Keyword saved!")
    def Load(self, path="./keywords.json"):
        with open(path, "r") as myfile: 
            tmp=json.loads(myfile.read())
            self.keywords=tmp["keywords"]
        print("Keyword loaded!")
    @staticmethod
    def GetKeyowrds(x, okt=None,num=10,raw=False, tags=["Noun"]):
        stop_words = ['은', '는', '이', '가', '의', '들', '좀', '잘', '걍', '과', '도', '를', '으로', '자', '에', '와', '하다', '년', '명', '각', '하', '아', '것', '의', '수', '등', '한', '것', '그', '이', '고', '손', '로', '순']
        hangul = re.compile('[^ ㄱ-ㅣ가-힣+]')
        kokt=okt if okt is not None else Okt()
        res=[]
        for sentence in tqdm(x):
            # deacc=True removes punctuations
            art=hangul.sub(" ",sentence)
            lst=[i[0] for i in kokt.pos(art) if i[1] in tags]
            lst=[i for i in lst if i not in stop_words]
            res.append(lst)
        doc_tokenized = res
        dictionary = Dictionary()
        BoW_corpus = [dictionary.doc2bow(doc, allow_update=True) for doc in doc_tokenized]
        tfidf = TfidfModel(BoW_corpus, smartirs='ntc')
        give=[]
        for i,a in enumerate(x):
            keydoc=[]
            for doc in tfidf[BoW_corpus[i]]:
                id, freq=doc
                keydoc.append((dictionary[id], freq))
            keywords=sorted(keydoc,key=lambda k:k[1], reverse=True)
            n=num if num<len(keywords) else len(keywords)
            give.append([i[0] for i in keywords[:n]])
        return give if not raw else keywords
    def ExtractKeyword(self):
        #x가 기사들 데이터 dictionary 형태
        #return은 각 기사별로 태그되는 키워드와 카테고리의 어떤 무언가
        self.keywords={}
        keywords=self.GetKeyowrds([i["article"]["content"] for i in self.crawler._arts], num=10)
        for i, a in enumerate(self.crawler._arts):
            self.crawler._arts[i]["keyword"]=keywords[i]
            for j in keywords[i]:
                if j in self.keywords:
                    self.keywords[j].append(a["id"])
                else:
                    self.keywords.update({j:[a["id"]]})
        print("Extract keywords Done!")
    def ExtractKeywordsByArea(self, area):
        #area는 "서울" "대구" 이런 지역 검색어
        #문서당 3개씩 키워드를 뽑아서 하나로 합쳐서 많이 나오는 단어 리턴.
        a=self.crawler.GetSearchedArticles(area)
        urls=a[1]
        result=[]
        for i in tqdm(urls):
            #Return : (title, img(dict), article(string), date, topics)
            (tit, img, art, dat, tag)=self.crawler.CrawlArticle(i)
            if art==None:
                continue
            result.append(art)
            time.sleep(0.5)
            # twitter함수를 통해 읽어들인 내용의 형태소를 분석한다.
        k=self.GetKeyowrds(result,self.okt,raw=True, tags=["Noun"])
        return k
    def AreasToWordcloud(self):
        area=["서울", "부산", "인천"]#"대구", "인천", "광주", "대전", "울산", "제주"]
        for i in area:
            k=self.ExtractKeywordsByArea(i)
            if len(k)<0:
                return
            mask = np.array(Image.open('./mask.png'))
            wc = WordCloud(mode = "RGBA", background_color=None, font_path="Donoun Medium.ttf",width=400,height=400, mask=mask, )
            cloud = wc.generate_from_frequencies(dict(k))
            # 생성된 WordCloud를 test.jpg로 보낸다.
            cloud.to_file(f"{i}.png")
            time.sleep(4)
        print("WordCloud Update Done!")
    def KeywordView(self, x):
        #키워드별 최신 기사 상위 몇개를 반환 (id만)
        #크롤러에 접근하든가..
        #{title:"blah", desc:"blah", thumbnail:"blah", date:"blah", id:1}
        pol=self.keywords[x] if x in self.keywords else "대통령"
        latest=self.crawler.GetFilteredArticles(pol, num=20, order="latest")
        popular=self.crawler.GetFilteredArticles(pol, num=20, order="popular")
        return {"keyword":x, "latest":latest, "popular":popular}
    def RunDoc2vec(self):
        stop_words = ['은', '는', '이', '가', '의', '들', '좀', '잘', '걍', '과', '도', '를', '으로', '자', '에', '와', '하다', '년', '명', '각', '하', '아', '것', '의', '수', '등', '한', '다', '을', '만']
        hangul = re.compile('[^ ㄱ-ㅣ가-힣+]')
        tagged_corpus_list = []
        skipped_article=[]
        print("Doc2Vec Preprocessing...")
        for i in tqdm(self.crawler._arts):
            if len(i["article"]["content"])<=250:
                skipped_article.append(i)
                continue
            art=hangul.sub(" ",i["article"]["content"])
            art=hangul.sub(" ",i["title"])+" "+art
            lst=self.okt.morphs(art)
            lst=[i for i in lst if i not in stop_words]
            tagged_corpus_list.append(TaggedDocument(tags=[str(i["id"])], words=lst))
        print('문서의 수 :', len(tagged_corpus_list))
        self.model.build_vocab(tagged_corpus_list)
        self.model.train(tagged_corpus_list, total_examples=len(tagged_corpus_list), epochs=50)
        self.model.save('dart.doc2vec')
        print(f"Model train done! skipped article:{len(skipped_article)}")
    def CheckDuplicated(self):
        for k,v in self.keywords.items():
            self.keywords[k]=list(set(v))
        print("Done!")
    def SimilarArticle(self, id):
        #Get similar 3 articles from id article
        recom=self.model.dv.most_similar(str(id), topn=3)
        recomarr=[int(i[0]) for i in recom]
        print()
        return {"recommend":[self.crawler.GetRecommendFormat(recomarr[0]), self.crawler.GetRecommendFormat(recomarr[1]),self.crawler.GetRecommendFormat(recomarr[2])]}
    def KeywordsLists(self):
        return self.keywords.keys()
    def CategorizeKeywords(self, x):
        pass
    def LatestArticlesByCategory(self, category, num):
        #카테고리별로 최신 num개 리턴
        pass

def MakeHandlerClassFromArgv(keyword :Keyword, crawler :Crawler, flist, fimg, fpage, fpages):
    class CustomHandler(BaseHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            self.key=keyword
            self.crawl=crawler
            self.flist=flist
            self.fimg=fimg
            self.fpage=fpage
            self.fpages=fpages
            super(CustomHandler, self).__init__(*args, **kwargs)
        def get(self,path):
            fd=self.fpage.index(path)
            return self.fpages[fd]
        def send(self, id, attr, data):
            d=quote(json.dumps(data))
            self.wfile.write(f"<div id='{id}' {attr}='{d}'></div>".encode('utf-8'))
        def do_GET(self):
            result = urlparse(self.path)
            splited=result.path.split("/")
            if result.path=="/":
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.end_headers() 
                self.send("maindata","data-main",self.crawl.MainView())
                main=self.get("main.html")
                self.wfile.write(main)
            elif len(splited)>=3:
                if splited[1]=="article":
                    try:
                        art=int(splited[2])
                        self.send_response(200)
                        self.send_header('Content-Type', 'text/html; charset=utf-8')
                        self.end_headers()
                        self.send("articledata","data-article",self.crawl.GetItem(art))
                        a=self.get("article.html")
                        self.wfile.write(a)
                    except Exception as e:
                        self.send_error(404)
                elif splited[1]=="keyword":
                    try:
                        self.send_response(200)
                        self.send_header('Content-Type', 'text/html; charset=utf-8')
                        self.end_headers()
                        data=self.key.KeywordView(unquote(splited[2]))
                        self.send('keyworddata', 'data-keyword', data)
                        a=self.get("keyword.html")
                        self.wfile.write(a)
                    except Exception as e:
                        print(e)
                        self.send_error(404)
                elif splited[1]=="category":
                    try:
                        self.send_response(200)
                        self.send_header('Content-Type', 'text/html; charset=utf-8')
                        self.end_headers()
                        data=self.crawl.CategoryView(splited[2])
                        self.send('keyworddata', 'data-keyword', data)
                        a=self.get("keyword.html")
                        self.wfile.write(a)
                    except Exception as e:
                        print(e)
                        self.send_error(404)
            elif unquote(result.path.split("/")[1]) in self.flist:
                fd=self.flist.index(unquote(result.path.split("/")[1])) 
                filename=self.flist[fd]
                print(filename)
                self.send_response(200)
                if filename.split(".")[1]=="png":
                    self.send_header('Content-Type', 'image/png')
                elif filename.split(".")[1]=="jpg":
                    self.send_header('Content-Type', 'image/jpg')
                self.end_headers()
                self.wfile.write(self.fimg[fd])
            elif result.path=="/api":
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.end_headers()
                params = parse_qs(result.query)
                if "component" in params.keys() and "method" in params.keys() and "p" in params.keys():
                    self.HandleComponent(params["component"][0].replace("\"", ""), params["method"][0].replace("\"", ""), [i.replace("\"", "") for i in params["p"]])
                else:
                    self.send_error(400)
            else:
                self.send_error(404)
        def HandleComponent(self, comp, method, p):
            print("got", comp, method, p)
            if comp == "keyword":
                if method == "GetAreaKeywords":
                    self.wfile.write(json.dumps(self.key.GetAreaKeywords(p[0])))
                elif method == "GetKeywords":
                    self.wfile.write(json.dumps(self.key.GetKeyowrds()))
                elif method == "SimilarArticle":
                    self.wfile.write(quote(json.dumps(self.key.SimilarArticle(int(p[0])))).encode('utf-8'))
                elif method == "KeywordsLists":
                    self.wfile.write(json.dumps(list(self.key.KeywordsLists())).encode('utf-8'))
            elif comp == "crawler":
                if method == "GetHighestLC":
                    self.wfile.write(json.dumps(self.crawl.GetHighestLC(int(p[0]))).encode('utf-8'))
                elif method == "GetSimilarLC":
                    self.wfile.write(json.dumps(self.crawl.GetSimilarLC(int(p[0]))).encode('utf-8'))
            else:
                self.send_error(400)
    return CustomHandler
    
class ForkingHTTPServer(ThreadingMixIn, HTTPServer):
    pass

if not test:
    crawl=Crawler(webdriver_path=webdriver_path,jsonpath=jsonpath)
    crawl._arts.sort(key=lambda x: x['date'], reverse=True)
    for i in [crawl._arts[len(crawl._arts)-1]['date'], crawl._arts[0]['date']]:
        date=datetime.strptime(i, "%Y-%m-%d %H:%M:%S")
        a=datetime.today()-date
        print(f"{i} : {a.days}")
    key=Keyword(crawler=crawl)
    def read(path):
        with open(path, "rb") as f:
            return f.read()
    def readpage(path):
        with open(path, "r", encoding="utf8") as f:
            return f.read().encode('utf-8')
    flist=["koreaarea.png", "ph.jpg", "logo.png", "서울.png", "부산.png", "인천.png", "대전.png"]
    fimg=[]
    for i in flist:
        fimg.append(read(i))
    fpage=[ "main.html", "article.html", "keyword.html"]
    fpages=[]
    for i in fpage:
        print(i)
        fpages.append(readpage(i))
    
    HandlerClass = MakeHandlerClassFromArgv(key,crawl, flist, fimg, fpage, fpages)
    handler=HandlerClass
    httpd = ForkingHTTPServer(('0.0.0.0', port), handler)
    thread = threading.Thread(target = httpd.serve_forever)
    thread.daemon = True
    thread.start()
    def fin():
        httpd.shutdown()
    print(f'Server running on port:{port}')
    if train:
        crawl.category=crawl.GetCategoryItems()
        print("Category reload")
        key.RunDoc2vec()
        key.ExtractKeyword()
        crawl.Save()
        key.Save()
    while True:
        x = input('')
        a=x.split(" ")
        if x=="save":
            crawl.Save()
            key.Save()
        elif a[0]=="day":
            print("Proceed")
            try:
                t = threading.Thread(target=crawl.CrawlGoGO, args=(int(a[1]),int(a[2]),int(a[3])))
                t.daemon=True
                t.start()
            except Exception as e:
                print("Error occured while crawlgogo",e)
        elif x=="category":
            crawl.category=crawl.GetCategoryItems()
            print("Category reload")
        elif x=="word":
            key.AreasToWordcloud()
        elif x=="doc":
            key.RunDoc2vec()
        elif x=="key":
            key.ExtractKeyword()
        elif x=="valid":
            try:
                t = threading.Thread(target=crawl.CrawlValidate)
                t.daemon=True
                t.start()
            except Exception as e:
                print("Error occured while crawlvalidate",e)
        elif x=="check":
            c=Counter()
            for i in crawl._arts:
                c[i["date"].split(" ")[0]]+=1
            c=sorted(c.items())
            print(c)
        elif x=="dup":
            key.CheckDuplicated()
        elif x=="update":
            crawl.category=crawl.GetCategoryItems()
            print("Category reload")
            key.RunDoc2vec()
            key.ExtractKeyword()
            crawl.Save()
            key.Save()
else:
    test=Crawler(webdriver_path=webdriver_path,jsonpath=jsonpath)
    test.test()